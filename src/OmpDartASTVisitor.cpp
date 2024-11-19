#include "OmpDartASTVisitor.h"

#include "clang/AST/ParentMapContext.h"

//added by Junhyung Shim
#include "clang/Frontend/FrontendAction.h" //for Lexer

#include "CommonUtils.h"
#include <functional> 


using namespace clang;

OmpDartASTVisitor::OmpDartASTVisitor(CompilerInstance *CI, unsigned* drdPragmaLineNumber, std::unordered_map<std::string, std::string> *macros)
    : Context(&(CI->getASTContext())), SM(&(Context->getSourceManager())), CI(CI), 
    drdPragmaLineNumber(drdPragmaLineNumber), macros(macros) {
  LastKernel = NULL;
  LastFunction = NULL;
  //this->CR = std::make_unique<ControlRegions>().get();
}

bool OmpDartASTVisitor::inLastTargetRegion(SourceLocation Loc) {
  if (!LastKernel)
    return false;
  return LastKernel->contains(Loc);
}

bool OmpDartASTVisitor::inLastFunction(SourceLocation Loc) {
  if (!LastFunction)
    return false;
  return LastFunction->contains(Loc);
}

std::vector<DataTracker *> &OmpDartASTVisitor::getFunctionTrackers() {
  return FunctionTrackers;
}

std::vector<Kernel *> &OmpDartASTVisitor::getTargetRegions() { return Kernels; }

bool OmpDartASTVisitor::VisitStmt(Stmt *S) {
  LastStmt = S;
  return true;
}

bool OmpDartASTVisitor::VisitFunctionDecl(FunctionDecl *FD) {
  if (!FD->getBeginLoc().isValid() || !SM->isInMainFile(FD->getLocation()))
    return true;
  if (!FD->doesThisDeclarationHaveABody())
    return true;

  DataTracker *Tracker = new DataTracker(FD, Context);
  FunctionTrackers.push_back(Tracker);
  LastFunction = Tracker;
  return true;
}

bool OmpDartASTVisitor::VisitVarDecl(VarDecl *VD) {
  
  if (!VD->getLocation().isValid() || !SM->isInMainFile(VD->getLocation()))
    return true;
  
  std::string tempS = VD->getNameAsString();
  std::replace(tempS.begin(), tempS.end(), '.', '_');
  std::replace(tempS.begin(), tempS.end(), ' ', '_');
  if(tempS == "class")tempS = "_class";
  QualType QT = VD->getType();

    //philosophy: get the most recent value
    if (Expr *Init = VD->getInit()) {
        if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(Init)){
          int val = IL->getValue().getSExtValue();
          this->allVars[tempS] = std::to_string(val);
          //llvm::outs()<< "wrote " + tempS + " as " << val <<"\n"; 
        }else{ //not int
          SourceRange range = Init->getSourceRange();
          SourceLocation sLoc = range.getBegin();
          SourceLocation eLoc = range.getEnd();
          StringRef text = Lexer::getSourceText(CharSourceRange::getCharRange(sLoc,eLoc),*SM,LangOptions());
          std::string rhs = text.str();
          rhs = rhs.substr(rhs.find('=')+1);
          rhs = rhs.substr(0,rhs.find(';'));
          rhs.erase(std::remove_if(rhs.begin(), rhs.end(), ::isspace), rhs.end());
          if(this->macros->find(rhs) != this->macros->end()){ //has matching macro
            this->allVars[tempS] = rhs;
          }else{
            this->allVars[tempS] = "!";
          }
        }
    }else{
      this->allVars[tempS] = "!";
    }
      
  
  if (inLastTargetRegion(VD->getLocation())) {
    LastKernel->recordPrivate(VD);
    return true;
  }

  if (inLastFunction(VD->getLocation())) {
    LastFunction->recordLocal(VD);
    uint8_t Flags = VD->hasInit() ? A_WRONLY : A_NOP;
    LastFunction->recordAccess(VD, VD->getLocation(), LastStmt, Flags, true);
    return true;
  }
  

  return true;
}

bool OmpDartASTVisitor::VisitCallExpr(CallExpr *CE) {
  if (!CE->getBeginLoc().isValid() || !SM->isInMainFile(CE->getBeginLoc()))
    return true;
  if (!inLastFunction(CE->getBeginLoc()))
    return true;
  FunctionDecl *Callee = CE->getDirectCallee();
  if (!Callee)
    return true;

  LastFunction->recordCallExpr(CE);
  Expr **Args = CE->getArgs();

  for (int I = 0; I < Callee->getNumParams(); ++I) {
    DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Args[I]->IgnoreImpCasts());
    QualType ParamType = Callee->getParamDecl(I)->getType();
    if (!DRE) {
      // is a literal
      continue;
    }
    // else if (!SM->isInMainFile(SM->getSpellingLoc(DRE->getBeginLoc()))) {
    //   // is externed
    //   continue;
    // }

    ValueDecl *VD = DRE->getDecl();
    uint8_t AccessType;
    if ((ParamType->isPointerType() || ParamType->isReferenceType()) &&
        !isPtrOrRefToConst(ParamType)) {
      // passed by pointer/reference (to non-const)
      AccessType = A_UNKNOWN;
    } else {
      // passed by pointer/reference (to const) OR passed by value
      AccessType = A_RDONLY;
    }

    if (isMemDealloc(Callee) || isMemAlloc(Callee)) {
      // No need for data transfer when allocating (excluding calloc) or freeing
      // a memory.
      AccessType = A_NOP;
    }
    LastFunction->recordAccess(VD, DRE->getLocation(), CE, AccessType, true);
  }

  return true;
}

bool OmpDartASTVisitor::VisitBinaryOperator(BinaryOperator *BO) {
  if (!BO->getBeginLoc().isValid() || !SM->isInMainFile(BO->getBeginLoc()))
    return true;
  if (!BO->isAssignmentOp())
    return true;
  if (!inLastFunction(BO->getBeginLoc()))
    return true;

  const DeclRefExpr *DRE = getLeftmostDecl(BO);
  const ValueDecl *VD = DRE->getDecl();
  std::string tempS = VD->getNameAsString();
  std::replace(tempS.begin(), tempS.end(), '.', '_');
  std::replace(tempS.begin(), tempS.end(), ' ', '_');
  if(tempS == "class")tempS = "_class";

  std::string operation = BO->getOpcodeStr().str();
  operation.erase(std::remove_if(operation.begin(), operation.end(), ::isspace), operation.end());
  if(this->allVars.find(tempS) == this->allVars.end()){
    this->allVars[tempS] = "!";
  }else if(operation == "+=" || operation == "=" || operation == "-=" || operation == "*=" || operation == "/="){
    llvm::outs() << tempS <<"   " << operation <<"\n";
    this->allVars[tempS] = "!";
  }

  
  uint8_t AccessType;
  // Check to see if this value is read from the right hand side.
  if (BO->isCompoundAssignmentOp() || usedInStmt(BO->getRHS(), VD)) {
    // If value is read from the right hand side, then technically this is a
    // read, but chronologically it was read first. So mark as ReadWrite so that
    // we don't mistake this ValueDecl for being Writen to first.
    AccessType = A_RDWR;
  } else {
    AccessType = A_WRONLY;
  }

  LastFunction->recordAccess(VD, DRE->getLocation(), BO, AccessType, true);
  return true;
}

bool OmpDartASTVisitor::VisitUnaryOperator(UnaryOperator *UO) {
  if (!UO->getBeginLoc().isValid() || !SM->isInMainFile(UO->getBeginLoc()))
    return true;
  if (!(UO->isPostfix() || UO->isPrefix()))
    return true;
  if (!inLastFunction(UO->getBeginLoc()))
    return true;

  const DeclRefExpr *DRE = getLeftmostDecl(UO);
  const ValueDecl *VD = DRE->getDecl();

  LastFunction->recordAccess(VD, DRE->getLocation(), UO, A_RDWR, true);

  UnaryOperator::Opcode uop = UO->getOpcode();

  const Expr *e = UO->getSubExpr();
  if(const DeclRefExpr *dre = dyn_cast<DeclRefExpr>(e)){
    const ValueDecl *decl = dre->getDecl();
    std::string var = decl->getNameAsString();
    var.erase(std::remove_if(var.begin(), var.end(), ::isspace), var.end());
    if(this->allVars.find(var) != this->allVars.end()){
      if(uop == UO_PreInc || uop == UO_PostInc || uop == UO_PreDec || uop == UO_PostDec){
        this->allVars[var] = "!";
      }
    }else{
      this->allVars[var] = "!";
    }
  }
  
  return true;
}

bool OmpDartASTVisitor::VisitDeclRefExpr(DeclRefExpr *DRE) {
  if (!DRE->getBeginLoc().isValid() || !SM->isInMainFile(DRE->getBeginLoc()))
    return true;
  if (!inLastFunction(DRE->getBeginLoc()))
    return true;
  ValueDecl *VD = DRE->getDecl();
  if (!VD)
    return true;
  if (dyn_cast<clang::FunctionDecl>(VD))
    return true;

  LastFunction->recordAccess(VD, DRE->getLocation(), DRE, A_RDONLY, false);
  return true;
}

bool OmpDartASTVisitor::VisitArraySubscriptExpr(ArraySubscriptExpr *ASE) {
  if (!ASE->getBeginLoc().isValid() || !SM->isInMainFile(ASE->getBeginLoc()))
    return true;
  if (!inLastFunction(ASE->getBeginLoc()))
    return true;

  const ValueDecl *BasePointer = getLeftmostDecl(ASE)->getDecl();
  LastFunction->recordArrayAccess(BasePointer, ASE);
  return true;
}

bool OmpDartASTVisitor::VisitDoStmt(DoStmt *DS) {
  if (!DS->getBeginLoc().isValid() || !SM->isInMainFile(DS->getBeginLoc()))
    return true;
  if (!inLastFunction(DS->getBeginLoc()))
    return true;

  LastFunction->recordLoop(DS);
  return true;
}

bool OmpDartASTVisitor::VisitForStmt(ForStmt *FS) {
  if (!FS->getBeginLoc().isValid() || !SM->isInMainFile(FS->getBeginLoc()))
    return true;
  if (!inLastFunction(FS->getBeginLoc()))
    return true;

  LastFunction->recordLoop(FS);
  return true;
}

bool OmpDartASTVisitor::VisitWhileStmt(WhileStmt *WS) {
  if (!WS->getBeginLoc().isValid() || !SM->isInMainFile(WS->getBeginLoc()))
    return true;
  if (!inLastFunction(WS->getBeginLoc()))
    return true;

  LastFunction->recordLoop(WS);
  return true;
}

bool OmpDartASTVisitor::VisitIfStmt(IfStmt *IS) {
  if (!IS->getBeginLoc().isValid() || !SM->isInMainFile(IS->getBeginLoc()))
    return true;
  
  if (!inLastFunction(IS->getBeginLoc()))
    return true;

  LastFunction->recordCond(IS);
  return true;
}

bool OmpDartASTVisitor::VisitSwitchStmt(SwitchStmt *SS) {
  if (!SS->getBeginLoc().isValid() || !SM->isInMainFile(SS->getBeginLoc()))
    return true;
  if (!inLastFunction(SS->getBeginLoc()))
    return true;

  LastFunction->recordCond(SS);
  return true;
}

bool OmpDartASTVisitor::VisitOMPExecutableDirective(OMPExecutableDirective *S) {
  // Ignore if the statement is in System Header files
  if (!S->getBeginLoc().isValid() || !SM->isInMainFile(S->getBeginLoc()))
    return true;
  if (isaTargetKernel(S)) {
    LastKernel = new Kernel(S, LastFunction->getDecl(), Context);
    LastFunction->recordTargetRegion(LastKernel);
    Kernels.push_back(LastKernel);
    return true;
  }
  if (Kernels.size() > 0 && Kernels.back()->contains(S->getBeginLoc())) {
#if DEBUG_LEVEL >= 1
    llvm::outs() << "nested dir at"
                 << S->getBeginLoc().printToString(Context->getSourceManager())
                 << "\n";
#endif
    Kernels.back()->recordNestedDirective(S);
  }
  return true;
}
