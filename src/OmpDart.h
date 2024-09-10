#ifndef OMPDART_H
#define OMPDART_H


#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/FrontendPluginRegistry.h"

#include "OmpDartASTConsumer.h"
#include "DrdpragmaHandler.h"


class OmpDartASTAction : public PluginASTAction {
private:
  std::string OutFilePath;
  bool Aggressive = false;
  std::unique_ptr<DrdpragmaHandler> ptr;
  unsigned *lineNumber = NULL;
  
public:
    OmpDartASTAction() {
      this->ptr = std::make_unique<DrdpragmaHandler>();
      this->lineNumber = (unsigned*) malloc(sizeof(unsigned));
      this->ptr->lineNumber = this->lineNumber;
    }

protected:
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {
    Preprocessor &PP = CI.getPreprocessor();
    PP.AddPragmaHandler(ptr.get());
    
    return std::make_unique<OmpDartASTConsumer>(&CI, &OutFilePath, Aggressive);
  }
  
   

  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {
    for (unsigned i = 0, e = args.size(); i != e; ++i) {
#if DEBUG_LEVEL >= 1
      llvm::outs() << "arg " << i << ": " << args[i] << "\n";
#endif

      DiagnosticsEngine &D = CI.getDiagnostics();
      if (args[i] == "-o" || args[i] == "--output") {
        if (i + 1 >= e) {
          D.Report(
              D.getCustomDiagID(DiagnosticsEngine::Error, "missing argument"));
          return false;
        }
        ++i;
        // record output preference
        OutFilePath = args[i];
      }
      if (args[i] == "-h" || args[i] == "--help") {
        PrintHelp(llvm::errs());
        return false;
      }
      if (args[i] == "-a" || args[i] == "--aggressive-cross-function") {
        Aggressive = true;
      }
    }

    return true;
  }
  void PrintHelp(llvm::raw_ostream &ros) {
    ros << "TODO help goes here\n";
    return;
  }
  
  

}; // end class OmpDartASTAction

//this registers ompdart as a frontend plugin
static FrontendPluginRegistry::Add<OmpDartASTAction> X("ompdart",
                                                       "target data analysis");



#endif