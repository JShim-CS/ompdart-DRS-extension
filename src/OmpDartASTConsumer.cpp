#include "OmpDartASTConsumer.h"

#include "AnalysisUtils.h"
#include "DirectiveRewriter.h"
#include "OmpDart.h"

#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/ParentMapContext.h"


#include <string>
#include <stack>
#include <unordered_map>
#include <algorithm>
#include <cctype>  

using namespace clang;

OmpDartASTConsumer::OmpDartASTConsumer(CompilerInstance *CI,
                                       const std::string *OutFilePath,
                                       bool Aggressive, unsigned* drdPragmaLineNumber)
    : Context(&(CI->getASTContext())), SM(&(Context->getSourceManager())),
      Visitor(new OmpDartASTVisitor(CI,drdPragmaLineNumber)),
      FunctionTrackers(Visitor->getFunctionTrackers()),
      Kernels(Visitor->getTargetRegions()), drdPragmaLineNumber(drdPragmaLineNumber) {
  TheRewriter.setSourceMgr(*SM, Context->getLangOpts());

  this->OutFilePath = *OutFilePath;
  this->Aggressive = Aggressive;
  this->CI = CI;
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

  this->recordReadAndWrite();


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

std::string OmpDartASTConsumer::getConditionOfLoop(ForStmt &FS, std::string &indexV){
    Stmt *init = FS.getInit();
    Expr *inc = FS.getInc();
    Expr *cond = FS.getCond();
    bool invalid;

    SourceLocation initStartLocation = init->getBeginLoc();
    SourceLocation initEndLocation = init->getEndLoc();
    CharSourceRange initConditionRange = CharSourceRange::getTokenRange(initStartLocation,initEndLocation);
    StringRef initstr = Lexer::getSourceText(initConditionRange,*SM,(*CI).getLangOpts(),&invalid);

   

    SourceLocation condStartLocation = cond->getBeginLoc();
    SourceLocation condEndLocation = cond->getEndLoc();
    CharSourceRange condConditionRange = CharSourceRange::getTokenRange(condStartLocation,condEndLocation);
    StringRef condstr = Lexer::getSourceText(condConditionRange,*SM,(*CI).getLangOpts(),&invalid);

    std::string bound1 = initstr.str().substr(initstr.str().find('='));
    long b1 = 0;
    bool negative = false;
    
    
    for(char c : bound1){


      if(c == '-'){
         negative = true;
      }

      if(c >= '0' && c <= '9'){
        if(negative){
          b1 =  b1*10 - (c - '0');
        }else{
          b1 = b1*10 + (c - '0');
        } 
      }

    }
    
    std::string indexVar; 
    std::string bound2 = condstr.str();
    char code = 0;
    bool increment = false;
   
    if(bound2.find("<=") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find("<=") > bound2.find(indexVar)){
        code = 1;
        increment = true;
        indexVar = bound2.substr(0, bound2.find("<="));
        bound2 = bound2.substr(bound2.find("<="), bound2.size() - bound2.find("<="));
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = false;
        // 0 1 2 3 4 5 6 7 8 9   size = 10
        //           < =             size - 5 -2 = 3
        indexVar = bound2.substr(bound2.find("<=") + 2, bound2.size() - bound2.find("<=") - 2);
        bound2 = bound2.substr(0, bound2.find("<="));
      }
    }else if(bound2.find(">=") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find(">=") > bound2.find(indexVar)){
        code = 1;
        increment = false;
        indexVar = bound2.substr(0, bound2.find(">="));
        bound2 = bound2.substr(bound2.find(">="), bound2.size() - bound2.find(">="));
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = true;
        indexVar = bound2.substr(bound2.find(">=") + 2, bound2.size() - bound2.find(">=") - 2);
        bound2 = bound2.substr(0, bound2.find(">="));
      }
    }else if(bound2.find("<") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find("<") > bound2.find(indexVar)){
        code = 1;
        increment = true;
        indexVar = bound2.substr(0, bound2.find("<"));
        bound2 = bound2.substr(bound2.find("<"), bound2.size() - bound2.find("<"));
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = false;
        indexVar = bound2.substr(bound2.find("<") + 1, bound2.size() - bound2.find("<") - 1);
        bound2 = bound2.substr(0, bound2.find("<"));
      }
    }else if(bound2.find(">") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find(">") > bound2.find(indexVar)){
        code = 1;
        increment = false;
        indexVar = bound2.substr(0, bound2.find(">") - 1);
        bound2 = bound2.substr(bound2.find(">"), bound2.size() - bound2.find(">"));
        
      }else{//otherwise, indexVar is on the right side
        code = 2;
        increment = true;
        indexVar = bound2.substr(bound2.find(">") + 1, bound2.size() - bound2.find(">") - 1);
        bound2 = bound2.substr(0, bound2.find(">"));
      }
    }else{ //does not involve an inequality
      bound2 = bound2.substr(0,bound2.find(';'));
      indexV = indexVar + "";
      return bound2;
    }
    indexV = indexVar + "";
    llvm::outs() << "INDEX_VAR: " << indexVar << "\n";
    std::string tempIndexVar;
    for(char c : indexVar){
      if(c != ' '){
        tempIndexVar += c;
      }
    }
    indexVar = tempIndexVar;
    
    switch(code){
      case 1:
        if(increment){
          return "(" + indexVar  +" >= " + std::to_string(b1) + ") && "
              + "(" + indexVar +" "+ bound2 + ")";
        }else{
          return "(" + indexVar  +" <= " + std::to_string(b1) + ") && "
              + "(" + indexVar + " " + bound2 + ")";
        }

      case 2:
        if(increment){
          return "(" + indexVar  +" >= " + std::to_string(b1) + ") && "
              + "(" + bound2 + " " + indexVar +")";
        }else{
          return "(" + indexVar  +" <= " + std::to_string(b1) + ") && "
              + "(" + bound2 + " " + indexVar +  ")";
        }
        
    }

    return "";
  }

void OmpDartASTConsumer::recordReadAndWrite(){
  DataTracker *TargetFunction = NULL;

  llvm::outs() << "INSIDE CONSUMER CLASS line num is set to: " << this->drdPragmaLineNumber << "\n";
  for(DataTracker *DT : FunctionTrackers){
    std::vector<const Stmt*> loops = DT->getLoops();
    for(const Stmt* s : loops){
      llvm::outs() << "Checking lines: " << (*SM).getSpellingLineNumber(s->getBeginLoc()) << "\n";
      if((*SM).getSpellingLineNumber(s->getBeginLoc()) == *(this->drdPragmaLineNumber) + 1){
        TargetFunction = DT;
        break;
      }
    }
    if(TargetFunction)break;
  }

  //dive into targetFunction to map out the predicates of conditionals
  std::stack<Stmt*> predicates;
  std::vector<std::string> predicate_string;
  //std::stack<std::string> predicateStack;
  

  std::vector<std::string> indexEncodings;


  if(TargetFunction){
    std::vector<AccessInfo> ai = TargetFunction->getAccessLog();
    bool stillSearching = true;
    std::string indexV = "";
    int v = -1;
    std::stack<std::vector<std::string>> chainOfPredicates;
    const Stmt* mostRecentControlRegion;
    ForStmt* fs = NULL;
    for(AccessInfo a : ai){
      v++;
      //foundForLoop
      if(stillSearching && (*SM).getSpellingLineNumber(a.S->getBeginLoc()) == *(this->drdPragmaLineNumber) + 1){
        stillSearching = false;
        fs = const_cast<ForStmt* >(llvm::dyn_cast<ForStmt>(a.S));
        std::string str = this->getConditionOfLoop(*fs,indexV);
        indexV.erase(std::remove_if(indexV.begin(), indexV.end(), ::isspace), indexV.end());
        predicate_string.push_back(str);
        continue;
      }
      
      if(!stillSearching){
        if(a.Barrier == CondBegin || a.Barrier == CondCase || a.Barrier == CondFallback){
          mostRecentControlRegion = a.S;
          continue;
        }

        if(a.Flags == A_WRONLY || a.Flags == A_RDWR || a.Flags == A_RDONLY){
          bool invalid;
          SourceLocation bloc = a.S->getBeginLoc();
          SourceLocation eloc = a.S->getEndLoc();
          CharSourceRange arrRange = CharSourceRange::getTokenRange(bloc,eloc);
          StringRef sr =  Lexer::getSourceText(arrRange,*SM,(*CI).getLangOpts(),&invalid);
          std::string exp = sr.str();
          exp.erase(std::remove_if(exp.begin(), exp.end(), ::isspace), exp.end());
          
          if(exp == indexV)continue;


          const Expr *cond = NULL; //(dyn_cast<IfStmt>(a.S))->getCond();
          const auto &Parents = (CI->getASTContext()).getParents(DynTypedNode::create(*(a.S)));
          std::string condition = ""; 
          std::string requiredCondition = "";
          std::stack<const DynTypedNodeList*> nodeStack;
          std::stack<std::string> predicateStack;
          nodeStack.push(&Parents);
          const Stmt *elseIfStmt = NULL;
          const Stmt *firstPaernt = NULL;
          int loopCounter = 0;
          bool breakWhile = false;
          
          while(!nodeStack.empty()){
            const auto *tempParents = nodeStack.top();
            nodeStack.pop();
            const IfStmt* lastSeen = NULL;
            //llvm::outs()<<"while\n";
            for (const auto Parent : *tempParents){
              //llvm::outs()<<"for\n";
              
              
              const Stmt *stmt = Parent.get<Stmt>();
              if(stmt == fs->getBody()){
                breakWhile = true;
                break;
              }

              if(stmt){
                //if-regions only show parental hierarchy if 1. nested or 2. if-elseif-else
                if(const IfStmt* ifs = dyn_cast<IfStmt>(stmt)){
                  if(ifs == mostRecentControlRegion && !loopCounter){//this includes when in if()a=20; format
                    requiredCondition += this->recursivelySetTheString(ifs->getCond(),v,indexV);
                    loopCounter++;
                  }else if(lastSeen->getElse() == mostRecentControlRegion){ 
                    requiredCondition += " AND !(" + this->recursivelySetTheString(ifs->getCond(),v,indexV) + ")";
                    loopCounter++;
                  }
                  mostRecentControlRegion = (const Stmt*) ifs;
                }

                const auto &ThingToPush = (CI->getASTContext()).getParents(DynTypedNode::create(*stmt));
                nodeStack.push(&ThingToPush);
              }
            }
            if(breakWhile)break;
            
          }

          
          
          if(requiredCondition != ""){
            llvm::outs() <<  "(" << exp <<" requires: ";
            this->setArrayIndexEncoding(a.S,v,indexV,requiredCondition);
            llvm::outs() << requiredCondition << " ) ";
            if(a.ArraySubscript){
              const Expr *base = a.ArraySubscript->getBase();
              bloc = base->getBeginLoc();
              eloc = base->getEndLoc();
              arrRange = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
              sr = Lexer::getSourceText(arrRange,*SM,(*CI).getLangOpts(),&invalid);
              llvm::outs() << "array name is: " << sr.str() <<" ";
              //It is easier to get the array index from the source text
            }
            llvm::outs() << "\n";
           
            //requiredCondition = "";
          }
        }

      }
    }

    if(!stillSearching){
      llvm::outs() << "predicate String: " << predicate_string[0] << "\n";
      llvm::outs() << "indexVAR: " << indexV << "\n";
    }
    
  }

  llvm::outs() << "ADDITIONAL VARS:\n";
  for (const auto &pair : Visitor->allVars) {
    llvm::outs() << pair.first <<"\n";
  }
  llvm::outs()<< "WRITES:\n";
  for (const auto &pair : this->writeMap) {
    llvm::outs() << pair.first <<"\n";
  }

  llvm::outs()<< "READS:\n";
  for (const auto &pair : this->readMap) {
    llvm::outs() << pair.first <<"\n";
  }
}

std::string OmpDartASTConsumer::setStringForRegion(const Expr *exp, int v,  const std::string &indexV){
  return this->recursivelySetTheString(exp,v, indexV);
}

std::string OmpDartASTConsumer::recursivelySetTheString(const Expr *exp, int v, const std::string &indexV){
  if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(exp)){
    std::string op = binOp->getOpcodeStr().str();
    std::string right = this->recursivelySetTheString(binOp->getRHS(),v,indexV);
    std::string left = this->recursivelySetTheString(binOp->getLHS(),v,indexV);
    return left + " " + op + " " + right;
  }else if(const DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(exp)){
    //llvm::outs() << "inside" <<"\n";
    const clang::ValueDecl *decl = declRef->getDecl();

    std::string val = decl->getNameAsString();
    val.erase(std::remove_if(val.begin(), val.end(), ::isspace), val.end());
    if(val == indexV){
      return val + "_drdVar_" + std::to_string(v);
    }else{
      return val;
    }
  }else if (const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(exp)){
    const clang::Expr *childExpr = ice->getSubExpr();
    return this->recursivelySetTheString(childExpr,v,indexV);
  }else{
    SourceRange expRange = exp->getSourceRange();
    StringRef expText = Lexer::getSourceText(CharSourceRange::getTokenRange(expRange), 
                                              (*SM), (*CI).getLangOpts());

    return expText.str();
  }

}

std::string OmpDartASTConsumer::recursivelyFindArrayIndex(const Expr *exp, int v,  const std::string &indexV){
  
  if(const ArraySubscriptExpr *arrayExpr = dyn_cast<ArraySubscriptExpr>(exp)){
    const Expr *base = arrayExpr->getBase();
    SourceLocation bloc = base->getBeginLoc();
    SourceLocation eloc = base->getEndLoc();
    CharSourceRange arrayName = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
    bool invalid; //is this even needed??
    StringRef sr  = Lexer::getSourceText(arrayName,*SM,(*CI).getLangOpts(),&invalid);
    return sr.str() +";("+this->recursivelySetTheString(arrayExpr->getIdx(),v,indexV) +")";
  }else if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(exp)){
    std::string left = this->recursivelyFindArrayIndex(binOp->getLHS(),v,indexV);
    std::string right = this->recursivelyFindArrayIndex(binOp->getRHS(),v,indexV);
   
    if(left == "" && right == ""){
      return "";
    }else if(left != "" && right != ""){
     return "( (" + left + ") AND (" + right +") )"; 
    }else if(left != ""){
      return left;
    }else if(right != ""){
      return right;
    }
  }else if (const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(exp)){
    const clang::Expr *childExpr = ice->getSubExpr();
    return this->recursivelyFindArrayIndex(childExpr,v,indexV);
  }else{
    return "";
  }
}

void OmpDartASTConsumer::setArrayIndexEncoding(const Stmt *exp, int v, const std::string &indexV, const std::string controlCondition){
   if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(exp)){
    std::string op = binOp->getOpcodeStr().str();
    
    //check for write (left side) first
    if(const ArraySubscriptExpr *arrayExpr = dyn_cast<ArraySubscriptExpr>(binOp->getLHS())){
      int indexPos = 0;
      const Expr *base = arrayExpr->getBase();
      SourceLocation bloc = base->getBeginLoc();
      SourceLocation eloc = base->getEndLoc();
      CharSourceRange arrayName = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
      bool invalid; //is this even needed??
      StringRef sr  = Lexer::getSourceText(arrayName,*SM,(*CI).getLangOpts(),&invalid);
      std::string write = this->recursivelySetTheString(arrayExpr->getIdx(),v,indexV);
      this->writeMap[sr.str()+";("+write+"):"+controlCondition] = true;
    }

    std::string read =  this->recursivelyFindArrayIndex(binOp->getRHS(),v,indexV);
    if(read != ""){
      this->readMap[read+":"+controlCondition] = true;
    }
    
  }

}

