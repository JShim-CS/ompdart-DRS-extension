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
#include<iostream>
#include<fstream>
#include <memory>
#include <regex>



using namespace clang;

OmpDartASTConsumer::OmpDartASTConsumer(CompilerInstance *CI,
                                       const std::string *OutFilePath,
                                       bool Aggressive, unsigned* drdPragmaLineNumber, std::unordered_map<std::string, std::string> *macros)
    : Context(&(CI->getASTContext())), SM(&(Context->getSourceManager())),
      Visitor(new OmpDartASTVisitor(CI,drdPragmaLineNumber)),
      FunctionTrackers(Visitor->getFunctionTrackers()),
      Kernels(Visitor->getTargetRegions()), drdPragmaLineNumber(drdPragmaLineNumber), macros(macros) {
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


  this->recordReadAndWrite();
  
  //llvm::outs() << "[" << macros << "]" <<"\n";
  
  
}

std::string OmpDartASTConsumer::getConditionOfLoop(ForStmt &FS, std::string indexVar, std::unordered_map<std::string,bool> &indexV){
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

    std::string bound1 = initstr.str().substr(initstr.str().find('=')+1);
    long b1 = 0;
    bool negative = false;
    bool b1isVar = true;
    
    for(char c : bound1){


      if(c == '-'){
         negative = true;
      }

      if(c >= '0' && c <= '9'){
        if(negative){
          b1 =  b1*10 - (c - '0');
          b1isVar = false;
        }else{
          b1 = b1*10 + (c - '0');
          b1isVar = false;
        } 
      }

    }
     
    std::string bound2 = condstr.str();
    char code = 0;
    bool increment = false;
   
    if(bound2.find("<=") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find("<=") > bound2.find(indexVar)){
        code = 1; //loop var <= targetVar, Increment
        increment = true;
        indexVar = bound2.substr(0, bound2.find("<="));
        bound2 = bound2.substr(bound2.find("<="), bound2.size() - bound2.find("<="));
      }else{//otherwise, indexVar is on the right side
        code = 2;//2;// targetVar >= loopVar 
        increment = true;
        // 0 1 2 3 4 5 6 7 8 9   size = 10
        //           < =             size - 5 -2 = 3
        indexVar = bound2.substr(bound2.find("<=") + 2, bound2.size() - bound2.find("<=") - 2);
        bound2 = bound2.substr(0, bound2.find("<="));
      }
    }else if(bound2.find(">=") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find(">=") > bound2.find(indexVar)){  //  loopVar >=  targetVar
        code = 1;
        increment = false;
        indexVar = bound2.substr(0, bound2.find(">="));
        bound2 = bound2.substr(bound2.find(">="), bound2.size() - bound2.find(">="));
      }else{//otherwise, indexVar is on the right side    targetVar >= loopVar
        code = 2;
        increment = true;
        indexVar = bound2.substr(bound2.find(">=") + 2, bound2.size() - bound2.find(">=") - 2);
        bound2 = bound2.substr(0, bound2.find(">="));
      }
    }else if(bound2.find("<") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find("<") > bound2.find(indexVar)){ //loopVar < targetVar
        code = 1;
        increment = true;
        indexVar = bound2.substr(0, bound2.find("<"));
        bound2 = bound2.substr(bound2.find("<"), bound2.size() - bound2.find("<"));
      }else{//otherwise, indexVar is on the right side   targetVar < loopVar
        code = 2;
        increment = false;
        indexVar = bound2.substr(bound2.find("<") + 1, bound2.size() - bound2.find("<") - 1);
        bound2 = bound2.substr(0, bound2.find("<"));
      }
    }else if(bound2.find(">") != std::string::npos){
      //indexVar resides on the left side
      if(bound2.find(">") > bound2.find(indexVar)){ //     loopVar > targetVar
        code = 1;
        increment = false;
        indexVar = bound2.substr(0, bound2.find(">") - 1);
        bound2 = bound2.substr(bound2.find(">"), bound2.size() - bound2.find(">"));
        
      }else{//otherwise, indexVar is on the right side    targetVar > loopVar
        code = 2;
        increment = true;
        indexVar = bound2.substr(bound2.find(">") + 1, bound2.size() - bound2.find(">") - 1);
        bound2 = bound2.substr(0, bound2.find(">"));
      }
    }else{ //does not involve an inequality
      bound2 = bound2.substr(0,bound2.find(';'));
      indexVar.erase(std::remove_if(indexVar.begin(), indexVar.end(), ::isspace), indexVar.end());
      indexV[indexVar + ""] = true;
      return bound2;
    }
    indexVar.erase(std::remove_if(indexVar.begin(), indexVar.end(), ::isspace), indexVar.end());
    indexV[indexVar + ""] = true;
    // llvm::outs() << "INDEX_VAR: " << indexVar << "\n";
    // std::string tempIndexVar;
    // for(char c : indexVar){
    //   if(c != ' '){
    //     tempIndexVar += c;
    //   }
    // }
    // indexVar = tempIndexVar;
    std::string bb1 = b1isVar ? bound1 : std::to_string(b1);
    switch(code){
      case 1:
        if(increment){
          
          return "( XXX  >= " + bb1 + ") && "
              + "( XXX "+ bound2 + ")";
        }else{
           
          return "( XXX  <= " + bb1 + ") && "
              + "( XXX " + bound2 + ")";
        }

      case 2:
        if(increment){
          
          return "( XXX  >= " + bb1 + ") && "
              + "(" + bound2 + " XXX )";
        }else{
          
          return "( XXX <= " + bb1 + ") && "
              + "(" + bound2 + " XXX )";
        }
        
    }

    return "";
  }

std::string OmpDartASTConsumer::getLoopVariable(const ForStmt *fs){
  const Stmt* init = fs->getInc();
  std::string ret = "";
  if(const CompoundAssignOperator *cao = dyn_cast<CompoundAssignOperator>(init)){
     const Stmt* leftSide = cao->getLHS();
     if(const DeclRefExpr *dre = dyn_cast<DeclRefExpr>(leftSide)){
      const ValueDecl *decl = dre->getDecl();
      ret = decl->getNameAsString();
      ret.erase(std::remove_if(ret.begin(), ret.end(), ::isspace), ret.end());
     }
  }else if(const UnaryOperator *uop = dyn_cast<UnaryOperator>(init)){
     const Expr *e = uop->getSubExpr();
     if(const DeclRefExpr *dre = dyn_cast<DeclRefExpr>(e)){
      const ValueDecl *decl = dre->getDecl();
      ret = decl->getNameAsString();
      ret.erase(std::remove_if(ret.begin(), ret.end(), ::isspace), ret.end());
     }
  }
  return ret;
}
void OmpDartASTConsumer::recordReadAndWrite(){
  DataTracker *TargetFunction = NULL;

  llvm::outs() << "INSIDE CONSUMER CLASS line num is set to: " << *(this->drdPragmaLineNumber) << "\n";
  for(DataTracker *DT : FunctionTrackers){
    std::vector<const Stmt*> loops = DT->getLoops();
    for(const Stmt* s : loops){
      llvm::outs() << "Checking lines: " << (*SM).getSpellingLineNumber(s->getBeginLoc()) << "\n";
      if((*SM).getSpellingLineNumber(s->getBeginLoc()) == *(this->drdPragmaLineNumber) + 1){
        TargetFunction = DT;
        break;
      }
    }
    
    if(TargetFunction){
      break;
    }
  }

  //dive into targetFunction to map out the predicates of conditionals
  std::stack<Stmt*> predicates;
  //std::vector<std::string> predicate_string;
  std::unordered_map<std::string, std::string> loopVar2LoopPred;
  std::unordered_map<std::string, std::string> Encoded2Original;
  //std::stack<std::string> predicateStack;
  std::vector<std::string> differentiableIndexList;
  std::string diffIndex = "";
  std::unordered_map<std::string,bool> writtenMap;
  std::vector<std::string> indexEncodings;


  if(TargetFunction){
    std::vector<AccessInfo> ai = TargetFunction->getAccessLog();
    bool stillSearching = true;
    bool inTheTargetLoopRegion = false;
    std::unordered_map<std::string, bool> indexV;
    int v = -1;
    std::stack<std::vector<std::string>> chainOfPredicates;
    const Stmt* mostRecentControlRegion;
    //const Stmt* closestControlRegion;
    ForStmt* fs = NULL;
    for(AccessInfo a : ai){
      v++;
      //foundForLoop
      //llvm::outs()<<"EXECUTED44: " << (*SM).getSpellingLineNumber(a.S->getBeginLoc()) <<"\n";
      if(stillSearching && (*SM).getSpellingLineNumber(a.S->getBeginLoc()) == *(this->drdPragmaLineNumber) + 1){
        stillSearching = false;
        fs = const_cast<ForStmt* >(llvm::dyn_cast<ForStmt>(a.S));
        std::string loopVar = this->getLoopVariable(fs);
        std::string str = this->getConditionOfLoop(*fs,loopVar,indexV);
        //indexV.erase(std::remove_if(indexV.begin(), indexV.end(), ::isspace), indexV.end());
        str.erase(std::remove_if(str.begin(), str.end(), ::isspace), str.end());
        //predicate_string.push_back(str);
        loopVar2LoopPred[loopVar] = str;
        diffIndex = loopVar;
        llvm::outs() << loopVar <<" hit \n";
        //differentiableIndexList[loopVar] = {""};
        inTheTargetLoopRegion = true;
        continue;
      }
      
      if(!stillSearching && a.Barrier == LoopEnd)break;

      if(inTheTargetLoopRegion && a.Barrier == LoopBegin){
        fs = const_cast<ForStmt* >(llvm::dyn_cast<ForStmt>(a.S));
        std::string loopVar = this->getLoopVariable(fs);
        std::string str = this->getConditionOfLoop(*fs,loopVar,indexV);
        //indexV.erase(std::remove_if(indexV.begin(), indexV.end(), ::isspace), indexV.end());
        str.erase(std::remove_if(str.begin(), str.end(), ::isspace), str.end());
        //predicate_string.push_back(str);
        loopVar2LoopPred[loopVar] = str;
        continue;
      }

      
      
      if(!stillSearching){

        if(a.Barrier == CondBegin || a.Barrier == CondCase || a.Barrier == CondFallback){
          mostRecentControlRegion = a.S;
          //closestControlRegion = a.S;
          continue;
        }

        if(const clang::BinaryOperator *binOp = llvm::dyn_cast<clang::BinaryOperator>(a.S)){
          std::string op = binOp->getOpcodeStr().str();
          //if(op == "+=" || op == "-=" || op == "*=" || op == "/="){
          //  llvm::outs()<< "\nDATA RACE FROM ONE OF THE FOLLOWING COULD OCCUR: +=  -=  *=  /=\n";
          //  exit(0);
          //}
        }

        if(a.Flags == A_WRONLY || a.Flags == A_RDWR || a.Flags == A_RDONLY){
          bool invalid;
          SourceLocation bloc = a.S->getBeginLoc();
          SourceLocation eloc = a.S->getEndLoc();
          CharSourceRange arrRange = CharSourceRange::getTokenRange(bloc,eloc);
          StringRef sr =  Lexer::getSourceText(arrRange,*SM,(*CI).getLangOpts(),&invalid);
          std::string exp = sr.str();
          exp.erase(std::remove_if(exp.begin(), exp.end(), ::isspace), exp.end());
          
          //exp == indexV --> No need to track already tracked loop index variable
          if(indexV.find(exp) != indexV.end())continue;


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
            
            for (const auto Parent : *tempParents){
              const Stmt *stmt = Parent.get<Stmt>();
              if(stmt == fs->getBody()){
                breakWhile = true;
                break;
              }

              if(stmt){
                //if-regions only show parental hierarchy if 1. nested or 2. if-elseif-else
                if(const IfStmt* ifs = dyn_cast<IfStmt>(stmt)){
                  if(ifs == mostRecentControlRegion && !loopCounter){//this includes when in if()a=20; format
                    std::string tempS = this->recursivelySetTheString(ifs->getCond(),&v,indexV);
                    tempS = tempS.find('[') == std::string::npos ? tempS : "DRD_RANDOM_VAR";
                    requiredCondition += "(" +tempS +")";
                    loopCounter++;
                  }else if(ifs->getElse() == mostRecentControlRegion){ 
                    if(requiredCondition != ""){
                      requiredCondition += " AND ";
                    }
                    std::string tempCond = this->recursivelySetTheString(ifs->getCond(),&v,indexV);
                    tempCond = tempCond.find('[') == std::string::npos ? tempCond : "DRD_RANDOM_VAR";
                    if(tempCond.find("<=") != std::string::npos){
                      tempCond.replace(tempCond.find("<="),2,">");
                    }else if(tempCond.find(">=") != std::string::npos){
                      tempCond.replace(tempCond.find(">="),2,"<");
                    }else if(tempCond.find(">") != std::string::npos){
                      tempCond.replace(tempCond.find(">"),1,"<=");
                    }else if(tempCond.find("<") != std::string::npos){
                      tempCond.replace(tempCond.find("<"),1,">=");
                    }else if(tempCond.find("!=") != std::string::npos){
                      tempCond.replace(tempCond.find("!="),2,"==");
                    }else if(tempCond.find("==") != std::string::npos){
                      tempCond.replace(tempCond.find("=="),2,"!=");
                    }
                    requiredCondition += "(" + tempCond + ")";
                  }else{
                    if(requiredCondition != ""){
                      requiredCondition += " AND ";
                    }
                    requiredCondition += "(" +this->recursivelySetTheString(ifs->getCond(),&v,indexV) +")";
                  }
                }

                mostRecentControlRegion = stmt;
                const auto &ThingToPush = (CI->getASTContext()).getParents(DynTypedNode::create(*stmt));
                nodeStack.push(&ThingToPush);
              }
              
            }
            if(breakWhile)break;
          }

          
          
          //if(requiredCondition != ""){
            llvm::outs() <<  "(" << exp <<" requires: ";
            this->setArrayIndexEncoding(a.S,&v,indexV,requiredCondition,false,Encoded2Original);
            llvm::outs() << requiredCondition << " ) ";
            if(a.ArraySubscript){
              const Expr *base = a.ArraySubscript->getBase();
              bloc = base->getBeginLoc();
              eloc = base->getEndLoc();
              arrRange = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
              sr = Lexer::getSourceText(arrRange,*SM,(*CI).getLangOpts(),&invalid);
              llvm::outs() << "array name is: " << sr.str() <<" ";
              
            }
            llvm::outs() << "\n";
           
            //requiredCondition = "";
          //}
        }

      }
    }

    if(!stillSearching){
      //llvm::outs() << "predicate String: " << predicate_string[0] << "\n";
      //llvm::outs() << "indexVAR: " << indexV << "\n";
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

  std::ofstream outfile("drsolver.py");
  try{
    outfile <<"from z3 import *\n";
    outfile << "solver=Solver()\n";
    for (const auto &pair : Visitor->allVars) {
      outfile << pair.first + " = " + "Int(\""+pair.first+"\")\n";
    }
    outfile<< "DRD_RANDOM_VAR = Int(\"DRD_RANDOM_VAR\")\n";
    for(const auto &pair : *macros){
      //std::string rawInt = pair.second;
      //std::string rawMacro = pair.first;
      //rawMacro.erase(std::remove_if(rawMacro.begin(), rawMacro.end(), ::isspace), rawMacro.end());
      //rawInt.erase(std::remove_if(rawInt.begin(), rawInt.end(), ::isspace), rawInt.end());
      bool continueFirstLoop = false;
      llvm::outs()<<"IN READ AND WRITE: " << pair.second <<" THE END\n";
      for(char c : pair.second){
        if(c < '0' || c > '9'){
          continueFirstLoop = true;
          break;
        }
      }
      if(continueFirstLoop)continue;
      //if code makes past here, then the pragma indeed represents a number

      outfile << pair.first + " = Int(\"" + pair.first + "\")\n";
      outfile << "solver.add(" + pair.first + " == " + pair.second + ")\n";
    }
    
    int wr_counter = 0;
    std::vector<std::unique_ptr<std::vector<std::string>>> writeVector;
    for (const auto &pair : this->writeMap) {
      std::string info = pair.first;
      int pipeCounter = 0;
      std::string temp = "";
      std::string arrName = "";
      std::string arrIndex = "";
      //std::vector<std::string> loopVariableList;
      std::string condition = "";
      for(char c : info){//process string
        if(c == '|'){
          if(!pipeCounter){//if pipeCounter is zero
            arrName = temp;
            temp = "";
            pipeCounter++;
          }else if(pipeCounter == 1){
            arrIndex = temp;
            pipeCounter++;
            temp = "";
          }else if(pipeCounter == 2){
            //loopVariable = temp;
            //arrName | arrIndex | loopVars | condition
            pipeCounter++;
            temp = "";
          }
        }else{
          if(pipeCounter < 3){
            temp += c;
          }else{
            condition += c;
          }
        }
      }

      //arrName = arrName.find('[') == std::string::npos ? arrName : "DRD_RANDOM_VAR";
      //arrIndex = arrIndex.find('[') == std::string::npos ? arrIndex : "DRD_RANDOM_VAR";
      //loopVariable = loopVariable.find('[') == std::string::npos ? loopVariable : "DRD_RANDOM_VAR";
      //condition = condition.find('[') == std::string::npos ? condition : "DRD_RANDOM_VAR";

      llvm::outs()<<"Array Name : " << arrName <<"\n";
      llvm::outs()<<"Array Index : " << arrIndex <<"\n";
      //llvm::outs()<<"Loop Var : " << loopVariable <<"\n";
      llvm::outs()<<"Condition : " << condition <<"\n";

      //std::replace(arrIndex.begin(), arrIndex.end(), '(', ' ');
      //std::replace(arrIndex.begin(), arrIndex.end(), ')', ' ');
      //arrIndex.erase(std::remove_if(arrIndex.begin(), arrIndex.end(), ::isspace), arrIndex.end());

      condition.erase(std::remove_if(condition.begin(), condition.end(), ::isspace), condition.end());
      if(condition.find("<=") == std::string::npos && condition.find(">=") == std::string::npos
         && condition.find("<") == std::string::npos && condition.find(">") == std::string::npos 
         && condition.find("==") == std::string::npos && condition != "" && condition != "True" 
         && condition.find("!=") == std::string::npos && condition != "False"){
          condition = condition +"!= 0";
      }

      // for(std::string ilv2 : loopVariableList){
      //   std::string ilv = ilv2;
      //   ilv.erase(std::remove_if(ilv.begin(), ilv.end(), ::isspace), ilv.end());
      //   if(ilv == "")continue;
      //   outfile << ilv + " = Int(\"" + ilv +"\")\n";
      // }
      //outfile << loopVariable + " = Int(\"" + loopVariable +"\")\n";
      outfile << "wr_arr_index_" + std::to_string(wr_counter) + " = Int(\"" + "wr_arr_index_" + std::to_string(wr_counter) +"\")\n";
      
      for(auto p : loopVar2LoopPred){
        std::string loopVar = p.first;
        std::string encodedIndex = "";
        for(auto enc : Encoded2Original){
          if(writtenMap.find(enc.first) == writtenMap.end()){
            outfile << enc.first + " = Int(\"" + enc.first +"\")\n";
            writtenMap[enc.first] = true;
          }
          if(enc.second == loopVar){
            encodedIndex = enc.first;
            if(enc.second == diffIndex){
              differentiableIndexList.push_back(enc.first);
            }
            size_t firstPos = p.second.find("XXX");
            if(p.first != ""){
              std::string processedLoopPredicate = p.second;
              if(firstPos != std::string::npos){
                processedLoopPredicate.replace(firstPos,3,encodedIndex);
              }

              firstPos = processedLoopPredicate.find("&&");
              if(firstPos != std::string::npos){
                processedLoopPredicate.replace(firstPos,2,",");
              }

              firstPos = processedLoopPredicate.find("XXX");
              if(firstPos != std::string::npos){
                processedLoopPredicate.replace(firstPos,3,encodedIndex);
              }
              
              if(writtenMap.find(processedLoopPredicate) == writtenMap.end()){
                outfile << "solver.add(" + processedLoopPredicate+")\n";
                writtenMap[processedLoopPredicate] = true;
              }
              
               
            }

          }
        }

      }
      
      // outfile.close();
      // //dbg
      // exit(0);

      //quick dirty fix, fix it later
      if(condition == ""){
        condition = "True";
      }

      outfile << "wr_cond_"+ std::to_string(wr_counter) 
                + " = And ("+ "wr_arr_index_" + std::to_string(wr_counter)
               + " == " + arrIndex +", " + condition + ")\n";
      //outfile<<processedLoopPredicate<<"\n";

      // outfile.close();
      // //dbg
      // exit(0);

      writeVector.push_back(std::make_unique<std::vector<std::string>>());

      writeVector[wr_counter]->push_back("wr_cond_"+ std::to_string(wr_counter));
      writeVector[wr_counter]->push_back("wr_arr_index_" + std::to_string(wr_counter));
      writeVector[wr_counter]->push_back(arrName);

      wr_counter++;
    }
    int wawCount = 0;
    wr_counter = 0;
    std::unordered_map<std::string, bool> wawFinalConds;
    for(int i = 0; i < writeVector.size(); i++){
      for (int j = i+1; j < writeVector.size(); j++){
        if(writeVector[i]->at(2) != writeVector[j]->at(2))continue;
        wawFinalConds["waw_cond_" + std::to_string(wr_counter)] = true;
        outfile <<"waw_cond_" + std::to_string(wr_counter) 
                <<" = And( "+writeVector[i]->at(0) + ", (" + writeVector[i]->at(1) + " == " +writeVector[j]->at(1) + "), "
                << writeVector[j]->at(0) + ")\n";
        wawCount++;
        wr_counter++;
      }
    }
    if(wawCount>=1){
      outfile <<"waws = Or(";
    }else{
      outfile <<"waws = False\n";
    }
    
    wr_counter = 0;
    for (const auto &pair : wawFinalConds) {
      if(wr_counter == wawFinalConds.size()-1){
        outfile <<pair.first + ")\n";
      }else{
        outfile << pair.first +  ", ";
      }
      
      wr_counter++;
    }

    outfile<<"\n";

    int r_counter = 0;
    std::vector<std::unique_ptr<std::vector<std::string>>> readVector;
    for (const auto &pair : this->readMap) {
      std::string info = pair.first;
      int pipeCounter = 0;
      std::string temp = "";
      std::string arrName = "";
      std::string arrIndex = "";
      //std::vector<std::string> loopVariableList;
      std::string condition = "";
      for(char c : info){//process string
        if(c == '|'){
          if(!pipeCounter){//if pipeCounter is zero
            arrName = temp;
            temp = "";
            pipeCounter++;
          }else if(pipeCounter == 1){
            arrIndex = temp;
            pipeCounter++;
            temp = "";
          }else if(pipeCounter == 2){
            //loopVariable = temp;
            //arrName | arrIndex | loopVars | condition
            pipeCounter++;
            temp = "";
          }
        }else{
          if(pipeCounter < 3){
            temp += c;
          }else{
            condition += c;
          }
        }
      }

      

      
      outfile << "r_arr_index_" + std::to_string(r_counter) + " = Int(\"" + "r_arr_index_" + std::to_string(r_counter) +"\")\n";
      
      for(auto p : loopVar2LoopPred){
        std::string loopVar = p.first;
        std::string encodedIndex = "";
        for(auto enc : Encoded2Original){

          if(writtenMap.find(enc.first) == writtenMap.end()){
            outfile << enc.first + " = Int(\"" + enc.first +"\")\n";
            //llvm::outs() << enc.first << " ~~~~~~~~~~\n";
            writtenMap[enc.first] = true;
            
          }
          if(enc.second == loopVar){
            encodedIndex = enc.first;
            if(enc.second == diffIndex){
              differentiableIndexList.push_back(enc.first);
            }
            size_t firstPos = p.second.find("XXX");
            if(p.first != ""){
              std::string processedLoopPredicate = p.second;
              if(firstPos != std::string::npos){
                processedLoopPredicate.replace(firstPos,3,encodedIndex);
              }

              firstPos = processedLoopPredicate.find("&&");
              if(firstPos != std::string::npos){
                processedLoopPredicate.replace(firstPos,2,",");
              }

              firstPos = processedLoopPredicate.find("XXX");
              if(firstPos != std::string::npos){
                processedLoopPredicate.replace(firstPos,3,encodedIndex);
              }
              
              if(writtenMap.find(processedLoopPredicate) == writtenMap.end()){
                outfile << "solver.add(" + processedLoopPredicate+")\n";
                writtenMap[processedLoopPredicate] = true;
              }
              
               
            }

          }
        }

      }

      //quick dirty fix, fix it later
      if(condition == ""){
        condition = "True";
      }

      //if runtime value that cannot be computed, then mark as true
      condition = condition.find('[') == std::string::npos ? condition : "True";
      condition.erase(std::remove_if(condition.begin(), condition.end(), ::isspace), condition.end());
      if(condition.find("<=") == std::string::npos && condition.find(">=") == std::string::npos
         && condition.find("<") == std::string::npos && condition.find(">") == std::string::npos 
         && condition.find("==") == std::string::npos && condition.find("!=") == std::string::npos 
         &&condition != "" && condition != "True" && condition != "False"){
          
          condition = condition +"!= 0";
      }

      

      //if(writtenMap.find(arrIndex) == writtenMap.end()){
      // for(auto enc : Encoded2Original){
      //     if(writtenMap.find(enc.first) == writtenMap.end()){
      //       outfile << enc.first + " = Int(\"" + enc.first +"\")\n";
      //       //llvm::outs() << enc.first << " ~~~~~~~~~~\n";
      //       writtenMap[enc.first] = true;
      //     }
      // }
        std::string arrIndex2 = arrIndex;
        size_t rmpos = arrIndex2.find('(');
        if (rmpos != std::string::npos) {
          arrIndex2.erase(rmpos, 1);  // Remove one character at position 'pos'
        }
        rmpos = arrIndex2.find(')');
        if (rmpos != std::string::npos) {
          arrIndex2.erase(rmpos, 1);  // Remove one character at position 'pos'
        }


        //outfile << arrIndex2 << "= Int(\""+arrIndex2+"\")\n";
        //writtenMap[arrIndex] = true;
      //}
      outfile << "r_cond_"+ std::to_string(r_counter) 
                + " = And ("+ "r_arr_index_" + std::to_string(r_counter)
               + " == " + arrIndex +", " + condition + ")\n";
      //outfile<<processedLoopPredicate<<"\n";
      readVector.push_back(std::make_unique<std::vector<std::string>>());

      readVector[r_counter]->push_back("r_cond_"+ std::to_string(r_counter));
      readVector[r_counter]->push_back("r_arr_index_" + std::to_string(r_counter));
      //readVector[r_counter]->push_back(loopVariable);
      readVector[r_counter]->push_back(arrName);
      r_counter++;
    }

    int rawCount = 0;
    wr_counter = 0;
    std::unordered_map<std::string, bool> rawFinalConds;
    for(int i = 0; i < writeVector.size(); i++){
      for (int j = 0; j < readVector.size(); j++){
        if(readVector[j]->at(2) != writeVector[i]->at(2))continue;
        rawFinalConds["raw_cond_" + std::to_string(wr_counter)] = true;
        outfile <<"raw_cond_" + std::to_string(wr_counter) 
                <<" = And( "+writeVector[i]->at(0) + ", (" + writeVector[i]->at(1) + " == " +readVector[j]->at(1) + "), "
                << readVector[j]->at(0) + ")\n";
        rawCount++;
        wr_counter++;
      }
    }
    if(rawCount>=1){
      outfile <<"raws = Or(";
    }else{
      outfile <<"raws = False\n";
    }
    wr_counter = 0;
    for (const auto &pair : rawFinalConds) {
      if(wr_counter == rawFinalConds.size()-1){
        outfile <<pair.first + ")\n";
      }else{
        outfile << pair.first +  ", ";
      }
      wr_counter++;
    }

    std::vector<std::string> diffString;
    for(auto p : Encoded2Original){
      diffString.push_back(p.first);
    }
    for(int i = 0; i < diffString.size(); i++){
      for(int j = i+1; j < diffString.size(); j++){
        outfile << "solver.add(" + diffString[i] + " != " + diffString[j] +")\n";
      }
    }
    outfile<<"cstrnts = Or(waws,raws)\n";
    outfile << "solver.add(cstrnts)\n";
    outfile << "if solver.check() == z3.sat:\n";
    outfile << "\tprint(\"seems like data race(waw/raw/war) exists within the loop!\")\n";
    outfile <<"else:\n";
    outfile<<"\tprint(\"seems like no data race exists (please double check)\")\n";




    outfile.close();
    
  }catch(...){
    if(outfile){
      outfile.close();
    }
    llvm::outs() << "Error while solving for data race\n";
  }
  
  
 
  

  


}

std::string OmpDartASTConsumer::setStringForRegion(const Expr *exp, int *v,  std::unordered_map<std::string, bool> &indexV){
  return this->recursivelySetTheString(exp,v, indexV);
}

std::string OmpDartASTConsumer::recursivelySetTheString(const Expr *exp, int *v, std::unordered_map<std::string, bool> &indexV){
  if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(exp)){
    std::string op = binOp->getOpcodeStr().str();
    std::string right = this->recursivelySetTheString(binOp->getRHS(),v,indexV);
    std::string left = this->recursivelySetTheString(binOp->getLHS(),v,indexV);
    //llvm::outs() << "OP: " << op << "\n";
    if(op == "&&" || op == " && "){
      return "And(" + left +", " + right +")";
    }else if(op == "||" || op == " || "){
      return "Or(" + left +", " + right +")";
    } 
    return left + " " + op + " " + right;
  }else if(const DeclRefExpr *declRef = dyn_cast<DeclRefExpr>(exp)){
    //llvm::outs() << "inside" <<"\n";
    const clang::ValueDecl *decl = declRef->getDecl();

    std::string val = decl->getNameAsString();
    val.erase(std::remove_if(val.begin(), val.end(), ::isspace), val.end());
    if(indexV.find(val) != indexV.end()){
      return val + "_drdVar_" + std::to_string(*v);
    }else{
      return val;
    }
  }else if (const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(exp)){
    const clang::Expr *childExpr = ice->getSubExpr();
    return this->recursivelySetTheString(childExpr,v,indexV);
  }else if(const UnaryOperator *UOp = dyn_cast<UnaryOperator>(exp)){
    const Expr *e = UOp->getSubExpr();
    std::string uop = UOp->getOpcodeStr(UOp->getOpcode()).str();
    if(uop == "!"){
      uop = "Not ";
    }
    return uop + this->recursivelySetTheString(e, v, indexV);
  }else if(const ParenExpr *Pop = dyn_cast<ParenExpr>(exp)){
    const Expr *e = Pop->getSubExpr();
    return "("+this->recursivelySetTheString(e, v, indexV)+")";
  }else{
    SourceRange expRange = exp->getSourceRange();
    StringRef expText = Lexer::getSourceText(CharSourceRange::getTokenRange(expRange), 
                                              (*SM), (*CI).getLangOpts());

    return expText.str();
  }

}
//unused
// std::string OmpDartASTConsumer::recursivelyFindArrayIndex(const Expr *exp, int *v,  std::unordered_map<std::string, bool> &indexV){
//   //what is exp is another binOp??
//   if(const ArraySubscriptExpr *arrayExpr = dyn_cast<ArraySubscriptExpr>(exp)){
//     const Expr *base = arrayExpr->getBase();
//     SourceLocation bloc = base->getBeginLoc();
//     SourceLocation eloc = base->getEndLoc();
//     CharSourceRange arrayName = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
//     bool invalid; //is this even needed??
//     StringRef sr  = Lexer::getSourceText(arrayName,*SM,(*CI).getLangOpts(),&invalid);
//     // Arr_name | arr_index | loop Var
//     std::string loopVars = "";
//     for(auto lv : indexV){
//       loopVars = loopVars + "|" +lv.first+"_drdVar_"+std::to_string(*v);
//     }
//     if(loopVars == "")loopVars = "|";
//     return sr.str() +"|("+this->recursivelySetTheString(arrayExpr->getIdx(),v,indexV) +")"+loopVars;
//   }else if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(exp)){
//     std::string left = this->recursivelyFindArrayIndex(binOp->getLHS(),v,indexV);
//     std::string right = this->recursivelyFindArrayIndex(binOp->getRHS(),v,indexV);
//     std::string op = binOp->getOpcodeStr().str();
    
//     if(left == "" && right == ""){
//       return "";
//     }else if(left != "" && right != ""){
//       //std::string op = binOp->getOpcodeStr().str();
//       if(op == "="){
//         return left;
//       }else{
//         return left + " " + op + " " + right;  
//       }
//     }else if(left != ""){
//       return left;
//     }else if(right != ""){
//       return right;
//     }
//   }else if (const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(exp)){
//     const clang::Expr *childExpr = ice->getSubExpr();
//     return this->recursivelyFindArrayIndex(childExpr,v,indexV);
//   }else{
//     return "";
//   }
// }



//we need to update this method to support multiple arrays
void OmpDartASTConsumer::setArrayIndexEncoding(const Stmt *exp, int *v, std::unordered_map<std::string, bool> &indexV, const std::string controlCondition, bool isWrite, std::unordered_map<std::string,std::string> &Encoded2Original){
   if(const BinaryOperator *binOp = dyn_cast<BinaryOperator>(exp)){
    std::string op = binOp->getOpcodeStr().str();
    //llvm::outs() << "\nOOOPPPS: " << op <<"\n";
    std::string realCondition = controlCondition;
    //if the value cannot be determined, then mark it as true
    realCondition = realCondition.find('[') == std::string::npos ? realCondition : "True";
    //assume that the code is well-formatted
    if(controlCondition.find(" = ") != std::string::npos){ //control statement has assignment op as well
      //for over-approximation we set all assignment in the control statement predicate as true
      //if(a[i] = v){a[i+2]=0;} --> this could lead to datarace regardless of what the value of v is
      realCondition = "True";
    }
    
    //check for write (left side) first
    if(const ArraySubscriptExpr *arrayExpr = dyn_cast<ArraySubscriptExpr>(binOp->getLHS())){
      int indexPos = 0;
      const Expr *base = arrayExpr->getBase();
      SourceLocation bloc = base->getBeginLoc();
      SourceLocation eloc = base->getEndLoc();
      CharSourceRange arrayName = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
      bool invalid; //is this even needed??
      StringRef sr  = Lexer::getSourceText(arrayName,*SM,(*CI).getLangOpts(),&invalid);
      std::string wr = this->recursivelySetTheString(arrayExpr->getIdx(),v,indexV);
      wr = wr.find('[') == std::string::npos ? wr : "DRD_RANDOM_VAR";
      if(op == "="){
        //name |index | loopVar | condition
        std::string loopVar = "";
        for(auto lv : indexV){
          Encoded2Original[(lv.first+"_drdVar_"+std::to_string(*v))] = lv.first;
          loopVar = loopVar + "$" + (lv.first+"_drdVar_"+std::to_string(*v));
        }
        this->writeMap[sr.str()+"|("+wr+")|"+ loopVar+"|"+realCondition] = true;
      }else{
        std::string loopVar = "";
        for(auto lv : indexV){
          loopVar = loopVar + "$" + (lv.first+"_drdVar_"+std::to_string(*v));
          Encoded2Original[(lv.first+"_drdVar_"+std::to_string(*v))] = lv.first;
        }
        this->readMap[sr.str()+"|("+wr+")|"+ loopVar + "_drdVar_"+std::to_string(*v)+"|"+realCondition] = true;
      }
    }else if(const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(binOp->getLHS())){
      if(op == "="){
        this->setArrayIndexEncoding(ice->getSubExpr(),v,indexV,controlCondition,true,Encoded2Original);
      }else{
        this->setArrayIndexEncoding(ice->getSubExpr(),v,indexV,controlCondition,false,Encoded2Original);
      }
    }else{
      this->setArrayIndexEncoding(binOp->getLHS(),v,indexV,controlCondition,false,Encoded2Original);
    }

    *v += 1;


    if(const ArraySubscriptExpr *arrayExpr = dyn_cast<ArraySubscriptExpr>(binOp->getRHS())){
      int indexPos = 0;
      const Expr *base = arrayExpr->getBase();
      SourceLocation bloc = base->getBeginLoc();
      SourceLocation eloc = base->getEndLoc();
      CharSourceRange arrayName = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
      bool invalid; //is this even needed??
      StringRef sr  = Lexer::getSourceText(arrayName,*SM,(*CI).getLangOpts(),&invalid);
      std::string wr = this->recursivelySetTheString(arrayExpr->getIdx(),v,indexV);
      std::string loopVar = "";
      for(auto lv : indexV){
        loopVar = loopVar + "$" + (lv.first+"_drdVar_"+std::to_string(*v));
        Encoded2Original[(lv.first+"_drdVar_"+std::to_string(*v))] = lv.first;
      }
      this->readMap[sr.str()+"|("+wr+")|"+ loopVar+"|"+realCondition] = true;
      
    }else if(const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(binOp->getRHS())){
      this->setArrayIndexEncoding(ice->getSubExpr(),v,indexV,controlCondition,false,Encoded2Original);
    }else{
      this->setArrayIndexEncoding(binOp->getRHS(),v,indexV,controlCondition,false,Encoded2Original);
    }
    
  }else if(const UnaryOperator *UOp = dyn_cast<UnaryOperator>(exp)){
    this->setArrayIndexEncoding(UOp->getSubExpr(), v, indexV,controlCondition,false,Encoded2Original);
  }else if(const ParenExpr *Pop = dyn_cast<ParenExpr>(exp)){
    this->setArrayIndexEncoding(Pop->getSubExpr(), v, indexV,controlCondition,false,Encoded2Original);

  }else if(const ArraySubscriptExpr *arrayExpr = dyn_cast<ArraySubscriptExpr>(exp)){
      int indexPos = 0;
      const Expr *base = arrayExpr->getBase();
      SourceLocation bloc = base->getBeginLoc();
      SourceLocation eloc = base->getEndLoc();
      CharSourceRange arrayName = CharSourceRange::getTokenRange(bloc,eloc); // this time, arrRange gets the name of the array
      bool invalid; //is this even needed??
      StringRef sr  = Lexer::getSourceText(arrayName,*SM,(*CI).getLangOpts(),&invalid);
      std::string wr = this->recursivelySetTheString(arrayExpr->getIdx(),v,indexV);
      if(isWrite){
        std::string loopVar = "";
        for(auto lv : indexV){
          loopVar = loopVar + "$" + (lv.first+"_drdVar_"+std::to_string(*v));
          Encoded2Original[(lv.first+"_drdVar_"+std::to_string(*v))] = lv.first;
        }
        this->writeMap[sr.str()+"|("+wr+")|"+ loopVar+"|"+controlCondition] = true;
      }else{
        std::string loopVar = "";
        for(auto lv : indexV){
          loopVar = loopVar + "$" + (lv.first+"_drdVar_"+std::to_string(*v));
          Encoded2Original[(lv.first+"_drdVar_"+std::to_string(*v))] = lv.first;
        }
        this->readMap[sr.str()+"|("+wr+")|"+ loopVar +"|"+controlCondition] = true;
      }
  }

}

