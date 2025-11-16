/// \file
/// \brief Implementation of [Server Lifecycle].
/// [Server Lifecycle]:
/// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#lifeCycleMessages

#include "nixd-config.h"

#include "nixd/CommandLine/Configuration.h"
#include "nixd/CommandLine/Options.h"
#include "nixd/Controller/Controller.h"
#include "nixd/Eval/Launch.h"
#include "nixd/Support/Exception.h"

#include "lspserver/Protocol.h"

#include <llvm/Support/CommandLine.h>

#include <atomic>
#include <mutex>
#include <unordered_set>

using namespace nixd;
using namespace util;
using namespace llvm::json;
using namespace llvm::cl;
using namespace lspserver;

namespace {

opt<std::string> DefaultNixpkgsExpr{
    "nixpkgs-expr",
    desc("Default expression intrepreted as `import <nixpkgs> { }`"),
    cat(NixdCategory), init("import <nixpkgs> { }")};

opt<std::string> DefaultNixOSOptionsExpr{
    "nixos-options-expr",
    desc("Default expression interpreted as option declarations"),
    cat(NixdCategory),
    init("(let pkgs = import <nixpkgs> { }; in (pkgs.lib.evalModules { modules "
         "=  (import <nixpkgs/nixos/modules/module-list.nix>) ++ [ ({...}: { "
         "nixpkgs.hostPlatform = builtins.currentSystem;} ) ] ; })).options")};

opt<bool> EnableSemanticTokens{"semantic-tokens",
                               desc("Enable/Disable semantic tokens"),
                               init(false), cat(NixdCategory)};

// Here we try to wrap nixpkgs, nixos options in a single emtpy attrset in test.
std::string getDefaultNixpkgsExpr() {
  if (LitTest && !DefaultNixpkgsExpr.getNumOccurrences()) {
    return "{ }";
  }
  return DefaultNixpkgsExpr;
}

std::string getDefaultNixOSOptionsExpr() {
  if (LitTest && !DefaultNixOSOptionsExpr.getNumOccurrences()) {
    return "{ }";
  }
  return DefaultNixOSOptionsExpr;
}

} // namespace

void Controller::evalExprWithProgress(AttrSetClient &Client,
                                      const EvalExprParams &Params,
                                      std::string_view Description) {
  auto Token = rand();
  auto Action = [Token, Description = std::string(Description),
                 this](llvm::Expected<EvalExprResponse> Resp) {
    endWorkDoneProgress({
        .token = Token,
        .value = WorkDoneProgressEnd{.message = "evaluated " +
                                                std::string(Description)},
    });
    if (!Resp) {
      lspserver::elog("{0} eval expr: {1}", Description, Resp.takeError());
      return;
    }
    // If this is nixpkgs evaluation, build the function index
    if (Description == "nixpkgs entries") {
      buildNixpkgsIndex();
    }
  };
  createWorkDoneProgress({Token});
  beginWorkDoneProgress({.token = Token,
                         .value = WorkDoneProgressBegin{
                             .title = "evaluating " + std::string(Description),
                             .cancellable = false,
                             .percentage = false,
                         }});
  Client.evalExpr(Params, std::move(Action));
}

void Controller::buildNixpkgsIndex() {
  if (!nixpkgsClient()) {
    lspserver::log("Cannot build nixpkgs index: nixpkgs client not available");
    return;
  }

  lspserver::log("Building nixpkgs function index...");

  // Use shared state for async operations
  struct IndexState {
    std::unordered_set<std::string> Functions;
    std::atomic<size_t> TotalPending{0};
    std::mutex FunctionsLock;
  };
  auto State = std::make_shared<IndexState>();

  // Helper to index a scope (can be top-level or nested like "lib")
  auto indexScope = [this, State](const std::vector<std::string> &Scope,
                                  const std::string &ScopePrefix) {
    AttrPathCompleteParams Params{
        .Scope = Scope,
        .Prefix = "",
    };

    auto OnComplete = [this, ScopePrefix, Scope,
                       State](llvm::Expected<AttrPathCompleteResponse> Resp) {
      if (!Resp) {
        lspserver::elog("Failed to get {0} attributes for indexing: {1}",
                        ScopePrefix.empty() ? "nixpkgs" : ScopePrefix,
                        Resp.takeError());
        return;
      }

      State->TotalPending.fetch_add(Resp->size());

      // For each attribute, query its info to determine if it's a function
      for (const auto &Name : *Resp) {
        AttrPathInfoParams InfoParams;
        if (ScopePrefix.empty()) {
          InfoParams = {Name};
        } else {
          // For nested scopes, construct the full path
          auto ScopeVec = Scope;
          ScopeVec.push_back(Name);
          InfoParams = ScopeVec;
        }

        std::string FullName =
            ScopePrefix.empty() ? Name : ScopePrefix + "." + Name;

        auto OnInfo = [this, FullName,
                       State](llvm::Expected<AttrPathInfoResponse> InfoResp) {
          if (InfoResp) {
            // Check if it's a lambda (function)
            // nix::tLambda = 4 (from nix/src/libexpr/value.hh)
            if (InfoResp->Meta.Type == 4) {
              std::lock_guard _(State->FunctionsLock);
              State->Functions.insert(FullName);
            }
            // Also check if ValueDesc indicates it's a function (has arity)
            else if (InfoResp->ValueDesc && InfoResp->ValueDesc->Arity > 0) {
              std::lock_guard _(State->FunctionsLock);
              State->Functions.insert(FullName);
            }
          }

          // When all queries complete, update the index
          // Decrement and check if we were the one to reach 0
          if (State->TotalPending.fetch_sub(1) == 1) {
            std::lock_guard _(NixpkgsIndexLock);
            NixpkgsFunctions = std::move(State->Functions);
            lspserver::log("Nixpkgs index built: {0} functions",
                           NixpkgsFunctions.size());
          }
        };

        nixpkgsClient()->attrpathInfo(InfoParams, std::move(OnInfo));
      }
    };

    nixpkgsClient()->attrpathComplete(Params, std::move(OnComplete));
  };

  // Index top-level nixpkgs (fetchurl, writeShellApplication, etc.)
  indexScope({}, "");

  // Index lib.* (mkOption, mkIf, strings.*, attrsets.*, etc.)
  indexScope({"lib"}, "lib");
}

void Controller::
    onInitialize( // NOLINT(readability-convert-member-functions-to-static)
        [[maybe_unused]] const InitializeParams &Params,
        Callback<Value> Reply) {

  Object ServerCaps{
      {{"textDocumentSync",
        llvm::json::Object{
            {"openClose", true},
            {"change", (int)TextDocumentSyncKind::Incremental},
            {"save", true},
        }},
       {
           "codeActionProvider",
           Object{
               {"codeActionKinds", Array{CodeAction::QUICKFIX_KIND}},
               {"resolveProvider", false},
           },
       },
       {"definitionProvider", true},
       {"documentLinkProvider", Object{}},
       {"documentSymbolProvider", true},
       {"inlayHintProvider", true},
       {"completionProvider",
        Object{
            {"resolveProvider", true},
            {"triggerCharacters", {"."}},
        }},
       {"referencesProvider", true},
       {"documentHighlightProvider", true},
       {"hoverProvider", true},
       {"documentFormattingProvider", true},
       {"renameProvider",
        Object{
            {"prepareProvider", true},
        }},
       {"workspaceSymbolProvider", true}},
  };

  if (EnableSemanticTokens) {
    ServerCaps["semanticTokensProvider"] = Object{
        {
            "legend",
            Object{
                {"tokenTypes",
                 Array{
                     "function",  // function
                     "string",    // string
                     "number",    // number
                     "type",      // select
                     "keyword",   // builtin
                     "variable",  // constant
                     "interface", // fromWith
                     "variable",  // variable
                     "regexp",    // null
                     "macro",     // bool
                     "method",    // attrname
                     "regexp",    // lambdaArg
                     "regexp",    // lambdaFormal
                 }},
                {"tokenModifiers",
                 Array{
                     "static",   // builtin
                     "abstract", // deprecated
                     "async",    // dynamic
                 }},
            },
        },
        {"range", false},
        {"full", true},
    };
  }

  Object Result{{
      {"serverInfo",
       Object{
           {"name", "nixd"},
           {"version", NIXD_VERSION},
       }},
      {"capabilities", std::move(ServerCaps)},
  }};

  Reply(std::move(Result));

  ClientCaps = Params.capabilities;

  // Store workspace root for workspace-wide operations
  if (Params.rootUri)
    WorkspaceRoot = Params.rootUri->file().str();
  else if (Params.rootPath)
    WorkspaceRoot = *Params.rootPath;

  // Start default workers.
  startNixpkgs(NixpkgsEval);

  if (nixpkgsClient()) {
    evalExprWithProgress(*nixpkgsClient(), getDefaultNixpkgsExpr(),
                         "nixpkgs entries");
  }

  // Launch nixos worker also.
  {
    std::lock_guard _(OptionsLock);
    startOption("nixos", Options["nixos"]);

    if (AttrSetClient *Client = Options["nixos"]->client())
      evalExprWithProgress(*Client, getDefaultNixOSOptionsExpr(),
                           "nixos options");
  }
  try {
    Config = parseCLIConfig();
  } catch (LLVMErrorException &Err) {
    lspserver::elog("parse CLI config error: {0}, {1}", Err.what(),
                    Err.takeError());
    std::exit(-1);
  }
  fetchConfig();
}

void Controller::onInitialized(const lspserver::InitializedParams &Params) {}

void Controller::onShutdown(const lspserver::NoParams &,
                            lspserver::Callback<std::nullptr_t> Reply) {
  ReceivedShutdown = true;
  Reply(nullptr);
}
