/// \file
/// \brief Implementation of [Workspace Symbol].
/// [Workspace Symbol]:
/// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#workspace_symbol

#include "CheckReturn.h"
#include "Convert.h"

#include "nixd/Controller/Controller.h"

#include <boost/asio/post.hpp>
#include <llvm/ADT/StringRef.h>
#include <llvm/Support/Path.h>
#include <lspserver/Protocol.h>
#include <nixf/Basic/Nodes/Attrs.h>
#include <nixf/Basic/Nodes/Lambda.h>
#include <nixf/Parse/Parser.h>
#include <nixf/Sema/VariableLookup.h>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <string>

using namespace nixd;
using namespace lspserver;
using namespace nixf;

namespace {

std::string getLambdaName(const ExprLambda &Lambda) {
  if (!Lambda.arg() || !Lambda.arg()->id())
    return "(anonymous lambda)";
  return Lambda.arg()->id()->name();
}

/// Collect workspace symbols from AST.
void collectWorkspaceSymbols(
    const Node *AST, std::vector<SymbolInformation> &Symbols,
    const VariableLookupAnalysis &VLA, llvm::StringRef Src,
    llvm::StringRef FilePath, const std::string &Query,
    const std::unordered_set<std::string> *NixpkgsFunctions,
    const std::string &ContainerName = "") {
  if (!AST)
    return;

  auto matchesQuery = [&Query](const std::string &Name) {
    if (Query.empty())
      return true;
    // Case-insensitive substring search
    std::string LowerName = Name;
    std::string LowerQuery = Query;
    std::transform(LowerName.begin(), LowerName.end(), LowerName.begin(),
                   ::tolower);
    std::transform(LowerQuery.begin(), LowerQuery.end(), LowerQuery.begin(),
                   ::tolower);
    return LowerName.find(LowerQuery) != std::string::npos;
  };

  auto isNixpkgsFunction = [NixpkgsFunctions](const std::string &Name) {
    if (!NixpkgsFunctions)
      return false;
    return NixpkgsFunctions->count(Name) > 0;
  };

  switch (AST->kind()) {
  case Node::NK_ExprVar: {
    const auto &Var = static_cast<const ExprVar &>(*AST);
    std::string Name = Var.id().name();
    if (matchesQuery(Name)) {
      // Determine the symbol kind based on variable lookup analysis
      SymbolKind Kind = SymbolKind::Variable;
      auto Result = VLA.query(Var);
      using ResultKind = VariableLookupAnalysis::LookupResultKind;

      // Only add meaningful symbols
      if (Result.Kind == ResultKind::Defined && Result.Def) {
        // Classify based on definition source
        switch (Result.Def->source()) {
        case Definition::DS_Builtin:
          Kind = SymbolKind::Function; // Builtin functions
          break;
        case Definition::DS_LambdaArg:
        case Definition::DS_LambdaNoArg_Formal:
        case Definition::DS_LambdaWithArg_Arg:
        case Definition::DS_LambdaWithArg_Formal:
          Kind = SymbolKind::Variable; // Lambda parameters
          break;
        case Definition::DS_Let:
        case Definition::DS_Rec:
          // Check if it's a known nixpkgs function
          if (isNixpkgsFunction(Name)) {
            Kind = SymbolKind::Function;
          } else {
            Kind = SymbolKind::Constant; // Regular let/rec bindings
          }
          break;
        case Definition::DS_With:
          // Check nixpkgs index
          if (isNixpkgsFunction(Name)) {
            Kind = SymbolKind::Function;
          } else {
            Kind = SymbolKind::Variable; // Other with-scoped names
          }
          break;
        }

        SymbolInformation Sym{
            .name = Name,
            .kind = Kind,
            .location =
                {
                    .uri = URIForFile::canonicalize(FilePath, FilePath),
                    .range = toLSPRange(Src, Var.range()),
                },
            .containerName = ContainerName,
        };
        Symbols.emplace_back(std::move(Sym));
      } else if (Result.Kind == ResultKind::FromWith) {
        // Check nixpkgs index
        if (isNixpkgsFunction(Name)) {
          Kind = SymbolKind::Function;
        } else {
          Kind = SymbolKind::Variable;
        }

        SymbolInformation Sym{
            .name = Name,
            .kind = Kind,
            .location =
                {
                    .uri = URIForFile::canonicalize(FilePath, FilePath),
                    .range = toLSPRange(Src, Var.range()),
                },
            .containerName = ContainerName,
        };
        Symbols.emplace_back(std::move(Sym));
      }
    }
    break;
  }
  case Node::NK_ExprLambda: {
    const auto &Lambda = static_cast<const ExprLambda &>(*AST);
    std::string Name = getLambdaName(Lambda);
    if (matchesQuery(Name)) {
      SymbolInformation Sym{
          .name = Name,
          .kind = SymbolKind::Function,
          .location =
              {
                  .uri = URIForFile::canonicalize(FilePath, FilePath),
                  .range = toLSPRange(Src, Lambda.range()),
              },
          .containerName = ContainerName,
      };
      Symbols.emplace_back(std::move(Sym));
    }
    collectWorkspaceSymbols(Lambda.body(), Symbols, VLA, Src, FilePath, Query,
                            NixpkgsFunctions, Name);
    break;
  }
  case Node::NK_ExprAttrs: {
    const SemaAttrs &SA = static_cast<const ExprAttrs &>(*AST).sema();
    // Only process attribute definitions, not just names
    for (const auto &[Name, Attr] : SA.staticAttrs()) {
      if (!Attr.value())
        continue;

      // Create symbol for the attribute binding itself if it matches
      if (matchesQuery(Name)) {
        SymbolInformation Sym{
            .name = Name,
            .kind = SymbolKind::Key, // Attribute sets are key-value structures
            .location =
                {
                    .uri = URIForFile::canonicalize(FilePath, FilePath),
                    .range = toLSPRange(Src, Attr.key().range()),
                },
            .containerName = ContainerName,
        };
        Symbols.emplace_back(std::move(Sym));
      }

      // Recurse into the value with updated container name
      std::string NewContainer =
          ContainerName.empty() ? Name : ContainerName + "." + Name;
      collectWorkspaceSymbols(Attr.value(), Symbols, VLA, Src, FilePath, Query,
                              NixpkgsFunctions, NewContainer);
    }
    break;
  }
  default:
    for (const Node *Ch : AST->children())
      collectWorkspaceSymbols(Ch, Symbols, VLA, Src, FilePath, Query,
                              NixpkgsFunctions, ContainerName);
    break;
  }
}

void scanWorkspaceFiles(const std::string &RootPath,
                        std::vector<SymbolInformation> &Symbols,
                        const std::string &Query,
                        const std::unordered_set<std::string> *NixpkgsFunctions,
                        size_t MaxFiles = 1000) {
  namespace fs = std::filesystem;
  size_t FilesProcessed = 0;

  try {
    for (auto Entry : fs::recursive_directory_iterator(
             RootPath, fs::directory_options::skip_permission_denied)) {
      if (FilesProcessed >= MaxFiles)
        break;

      const auto &Path = Entry.path();

      // Early prune excluded directories
      if (Entry.is_directory()) {
        std::string DirName = Path.filename().string();
        if (DirName == ".git" || DirName == ".direnv" ||
            DirName == "result" || DirName == "node_modules") {
          Entry.disable_recursion_pending();
          continue;
        }
      }

      if (!Entry.is_regular_file())
        continue;

      if (Path.extension() != ".nix")
        continue;

      std::string PathStr = Path.string();

      FilesProcessed++;

      // Read file content
      std::ifstream File(Path);
      if (!File)
        continue;

      std::string Content((std::istreambuf_iterator<char>(File)),
                          std::istreambuf_iterator<char>());

      // Parse the file
      std::vector<nixf::Diagnostic> Diagnostics;
      std::shared_ptr<nixf::Node> AST = nixf::parse(Content, Diagnostics);

      if (!AST)
        continue;

      // Perform variable lookup analysis
      auto VLA = std::make_unique<nixf::VariableLookupAnalysis>(Diagnostics);
      VLA->runOnAST(*AST);

      // Collect symbols
      collectWorkspaceSymbols(AST.get(), Symbols, *VLA, Content, PathStr, Query,
                              NixpkgsFunctions);
    }
  } catch (const fs::filesystem_error &) {
    // Ignore filesystem errors (permission denied, etc.)
  }
}

} // namespace

void Controller::onWorkspaceSymbol(
    const WorkspaceSymbolParams &Params,
    Callback<std::vector<SymbolInformation>> Reply) {
  using CheckTy = std::vector<SymbolInformation>;
  auto Action = [Reply = std::move(Reply), Query = Params.query,
                 Limit = Params.limit, WorkspaceRoot = this->WorkspaceRoot,
                 ClientCaps = this->ClientCaps, this]() mutable {
    return Reply([&]() -> llvm::Expected<CheckTy> {
      std::vector<SymbolInformation> Symbols;

      // Require at least 2 characters to avoid scanning entire workspace,
      // prevents expensive operations on empty queries
      const size_t MinQueryLength = 2;

      if (Query.length() < MinQueryLength) {
        // Return empty result - client should wait for more input
        return Symbols;
      }

      // Get a pointer to the nixpkgs index (thread-safe read)
      const std::unordered_set<std::string> *NixpkgsFunctionsPtr = nullptr;
      {
        std::lock_guard G(NixpkgsIndexLock);
        if (!NixpkgsFunctions.empty())
          NixpkgsFunctionsPtr = &NixpkgsFunctions;
      }

      // First, collect from open documents
      {
        std::lock_guard G(TUsLock);
        for (const auto &Entry : TUs) {
          const auto &FilePath = Entry.getKey();
          const auto &TU = Entry.getValue();
          if (!TU || !TU->ast())
            continue;
          collectWorkspaceSymbols(TU->ast().get(), Symbols,
                                  *TU->variableLookup(), TU->src(), FilePath,
                                  Query, NixpkgsFunctionsPtr);
        }
      }

      // Then scan workspace files if we have a workspace root
      if (WorkspaceRoot) {
        scanWorkspaceFiles(*WorkspaceRoot, Symbols, Query, NixpkgsFunctionsPtr);
      }

      // Adjust symbol kinds to client capabilities if specified
      if (ClientCaps.WorkspaceSymbolKinds) {
        for (auto &Sym : Symbols) {
          Sym.kind = adjustKindToCapability(Sym.kind,
                                            *ClientCaps.WorkspaceSymbolKinds);
        }
      }

      // Apply limit if specified
      if (Limit && *Limit > 0 && Symbols.size() > static_cast<size_t>(*Limit)) {
        Symbols.resize(*Limit);
      }

      return Symbols;
    }());
  };
  boost::asio::post(Pool, std::move(Action));
}
