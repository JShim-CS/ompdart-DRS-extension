#include "OmpDartASTConsumer.h"

#include "AnalysisUtils.h"
#include "DirectiveRewriter.h"
#include "OmpDart.h"


#include <string>
#include <stack>

using namespace clang;

OmpDartASTConsumer::OmpDartASTConsumer(CompilerInstance *CI,
                                       const std::string *OutFilePath,
                                       bool Aggressive, unsigned* drdPragmaLineNumber)
    : Context(&(CI->getASTContext())), SM(&(Context->getSourceManager())),
      Visitor(new OmpDartASTVisitor(CI,drdPragmaLineNumber)),
      FunctionTrackers(Visitor->getFunctionTrackers()),
      Kernels(Visitor->getTargetRegions()) {
  TheRewriter.setSourceMgr(*SM, Context->getLangOpts());

  this->OutFilePath = *OutFilePath;
  this->Aggressive = Aggressive;
  this->CI = CI;
  this->drdPragmaLineNumber = 7;//*drdPragmaLineNumber;
}

void OmpDartASTConsumer::HandleTranslationUnit(ASTContext &Context) {
  this->CI->getPreprocessor();
  
  Visitor->TraverseDecl(Context.getTranslationUnitDecl());

  performInterproceduralAnalysis(FunctionTrackers);

  for (DataTracker *DT : FunctionTrackers) {
    DT->classifyOffloadedOps();
  }

  if (Aggressive)
    performAggressiveCrossFunctionOffloading(FunctionTrackers);

#if DEBUG_LEVEL >= 1
  llvm::outs() << "\n=========================================================="
                  "======================\n";
#endif
  for (DataTracker *DT : FunctionTrackers) {
    // DT->classifyOffloadedOps();
#if DEBUG_LEVEL >= 1
    DT->printAccessLog();
#endif
    // computes data mappings for the scope of single target regions
    DT->naiveAnalyze();
    // computes data mappings
    DT->analyze();
#if DEBUG_LEVEL >= 1
    llvm::outs() << "globals\n";
    for (auto Global : DT->getGlobals()) {
      llvm::outs() << "  " << Global->getNameAsString() << "  "
                   << Global->getID() << "\n";
    }
    llvm::outs() << "locals\n";
    for (auto Local : DT->getLocals()) {
      llvm::outs() << "  " << Local->getNameAsString() << "  " << Local->getID()
                   << "\n";
    }
#endif
  }

#if DEBUG_LEVEL >= 1
  llvm::outs() << "Number of Target Data Regions: " << Kernels.size() << "\n";

  // Print naive kernel information
  for (int I = 0; I < Kernels.size(); ++I) {
    llvm::outs() << "\nTargetRegion #" << I;
    Kernels[I]->print(llvm::outs(), *SM);
  }

  int I = 0;
#endif
  for (DataTracker *DT : FunctionTrackers) {
    const TargetDataRegion *Scope = DT->getTargetDataScope();
    if (!Scope)
      continue;
#if DEBUG_LEVEL >= 1
    llvm::outs() << "\nTargetScope #" << I++;
    Scope->print(llvm::outs(), *SM);
#endif
    rewriteTargetDataRegion(TheRewriter, Context, Scope);
  }

  DataTracker *TargetFunction = NULL;

  llvm::outs() << "INSIDE CONSUMER CLASS line num is set to: " << this->drdPragmaLineNumber << "\n";
  for(DataTracker *DT : FunctionTrackers){
    std::vector<const Stmt*> loops = DT->getLoops();
    for(const Stmt* s : loops){
      llvm::outs() << "Checking lines: " << (*SM).getSpellingLineNumber(s->getBeginLoc()) << "\n";
      if((*SM).getSpellingLineNumber(s->getBeginLoc()) == this->drdPragmaLineNumber + 1){
        TargetFunction = DT;
        break;
      }
    }
    if(TargetFunction)break;
  }

  //dive into targetFunction to map out the predicates of conditionals
  std::stack<Stmt*> predicates;
  std::vector<std::string> predicate_string;

  if(TargetFunction){
    std::vector<AccessInfo> ai = TargetFunction->getAccessLog();
    bool stillSearching = true;
    for(AccessInfo a : ai){
      //foundForLoop
      if(stillSearching && (*SM).getSpellingLineNumber(a.S->getBeginLoc()) == this->drdPragmaLineNumber + 1){
        stillSearching = false;
        
        ForStmt* fs = const_cast<ForStmt* >(llvm::dyn_cast<ForStmt>(a.S));
        std::string str = this->getConditionOfLoop(*fs);
        predicate_string.push_back(str);
        break;
      }
      if(!stillSearching)break;
    }

    if(!stillSearching){
      llvm::outs() << "predicate String: " << predicate_string[0] << "\n";
    }
    
  }


#if DEBUG_LEVEL >= 1
  for (DataTracker *DT : FunctionTrackers) {
    const FunctionDecl *funcDecl = DT->getDecl();
    Stmt *funcBody = funcDecl->getBody();
    static std::unique_ptr<CFG> sourceCFG =
        CFG::buildCFG(funcDecl, funcBody, &Context, clang::CFG::BuildOptions());
    auto langOpt = Context.getLangOpts();
    sourceCFG->dump(langOpt, true);
  }
#endif

  FileID FID = SM->getMainFileID();
  if (OutFilePath.empty()) {
    std::string ParsedFilename =
        SM->getFilename(SM->getLocForStartOfFile(FID)).str();
    char *CParsedFilename = strdup(ParsedFilename.c_str());
    char *Basename = basename(CParsedFilename);

    OutFilePath = "/tmp/" + std::string(Basename);
    free(CParsedFilename);
  }
  llvm::outs() << "Modified File at " << OutFilePath << "\n";
  std::error_code ErrorCode;
  llvm::raw_fd_ostream OutFile(OutFilePath, ErrorCode, llvm::sys::fs::OF_None);
  if (!ErrorCode) {
    // print to terminal
    // TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
    // write to OutFile
    TheRewriter.getEditBuffer(FID).write(OutFile);
  } else {
    llvm::outs() << "Could not create file\n";
  }
  OutFile.close();
}

std::string OmpDartASTConsumer::getConditionOfLoop(ForStmt &FS){
    Stmt *init = FS.getInit();
    Expr *inc = FS.getInc();
    Expr *cond = FS.getCond();
    bool invalid;

    SourceLocation initStartLocation = init->getBeginLoc();
    SourceLocation initEndLocation = init->getEndLoc();
    CharSourceRange initConditionRange = CharSourceRange::getTokenRange(initStartLocation,initEndLocation);
    StringRef initstr = Lexer::getSourceText(initConditionRange,*SM,(*CI).getLangOpts(),&invalid);

    // Don't need it for now
    // SourceLocation incStartLocation = inc->getBeginLoc();
    // SourceLocation incEndLocation = inc->getEndLoc();
    // CharSourceRange incConditionRange = CharSourceRange::getTokenRange(incStartLocation,incEndLocation);
    // StringRef incstr = Lexer::getSourceText(incConditionRange,*SM,(*CI).getLangOpts(),&invalid);


    SourceLocation condStartLocation = cond->getBeginLoc();
    SourceLocation condEndLocation = cond->getEndLoc();
    CharSourceRange condConditionRange = CharSourceRange::getTokenRange(condStartLocation,condEndLocation);
    StringRef condstr = Lexer::getSourceText(condConditionRange,*SM,(*CI).getLangOpts(),&invalid);

    std::string bound1 = initstr.str().substr(initstr.str().find('='));
    long b1 = 1;
    
    
    for(char c : bound1){


      if(c == '-'){
        b1 *= -1;
      }

      if(c >= '0' && c <= '9'){
        if(b1 < 0){
          b1 =  b1*10 - ('c' - '0');
        }else{
          b1 = b1*10 + ('c' - '0');
        } 
      }

    }
    //FS.getConditionVariable();
    //llvm::outs() <<"EXECUTED: " << FS.getConditionVariable()->getName().str() <<"\n";
    std::string indexVar = "i"; //FS.getConditionVariable()->getName().str();
    std::string bound2 = condstr.str();
    char code = 0;
    bool increment = false;
   
    if(bound2.find("<=") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find("<=") > bound2.find(indexVar)){
        code = 1;
        increment = true;
        bound2 = bound2.substr(bound2.find("<="), bound2.size() - bound2.find("<=") - 1);
        
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = false;
        bound2 = bound2.substr(0, bound2.find("<=") -1);
      }
    }else if(bound2.find(">=") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find(">=") > bound2.find(indexVar)){
        code = 1;
        increment = false;
        bound2 = bound2.substr(bound2.find(">="), bound2.size() - bound2.find(">=") - 1);
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = true;
        bound2 = bound2.substr(0, bound2.find(">=") -1);
      }
    }else if(bound2.find("<") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find("<") > bound2.find(indexVar)){
        code = 1;
        increment = true;
        bound2 = bound2.substr(bound2.find("<"), bound2.size() - bound2.find("<") - 1);
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = false;
        bound2 = bound2.substr(0, bound2.find("<") -1);
      }
    }else if(bound2.find(">") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find(">") > bound2.find(indexVar)){
        code = 1;
        increment = false;
        bound2 = bound2.substr(bound2.find(">"), bound2.size() - bound2.find(">") - 1);
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = true;
        bound2 = bound2.substr(0, bound2.find(">") -1);
      }
    }else{ //does not involve an inequality
      bound2 = bound2.substr(0,bound2.find(';'));
      return bound2;
    }

    
    switch(code){
      case 1:
        if(increment){
          return "(" + indexVar  +" >= " + std::to_string(b1) + ") && "
              + "(" + indexVar + bound2 + ")";
        }else{
          return "(" + indexVar  +" <= " + std::to_string(b1) + ") && "
              + "(" + indexVar + bound2 + ")";
        }

      case 2:
        if(increment){
          return "(" + indexVar  +" >= " + std::to_string(b1) + ") && "
              + "(" + bound2 + indexVar +")";
        }else{
          return "(" + indexVar  +" <= " + std::to_string(b1) + ") && "
              + "(" + bound2 + indexVar +  ")";
        }
        
    }

    return "";
  }
