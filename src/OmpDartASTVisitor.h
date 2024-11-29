#ifndef ROSEASTVISITOR_H
#define ROSEASTVISITOR_H

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"

#include "DataTracker.h"
#include "DrdpragmaHandler.h"
#include "ControlRegions.h"
#include <unordered_map>

using namespace clang;

class OmpDartASTVisitor : public RecursiveASTVisitor<OmpDartASTVisitor> {
private:
  ASTContext *Context;
  SourceManager *SM;
  //added by Junhyung Shim
  CompilerInstance *CI;
  unsigned* drdPragmaLineNumber; 
  ControlRegions *CR;


  // each DataTracker keeps track of data access within the scope of a single
  // function
  std::vector<DataTracker *> FunctionTrackers;
  std::vector<Kernel *> Kernels;
  DataTracker *LastFunction;
  Kernel *LastKernel;
  Stmt *LastStmt;

  bool inLastTargetRegion(SourceLocation Loc);
  bool inLastFunction(SourceLocation Loc);


public:
  
  std::unordered_map<std::string,std::string> allVars;
  explicit OmpDartASTVisitor(CompilerInstance *CI, unsigned* drdPragmaLineNumber,std::unordered_map<std::string,std::string> *macros);
  std::unordered_map<std::string,std::string> *macros;
  std::vector<DataTracker *> &getFunctionTrackers();
  std::vector<Kernel *> &getTargetRegions(); 

  virtual bool VisitStmt(Stmt *S);
  virtual bool VisitFunctionDecl(FunctionDecl *FD);
  virtual bool VisitVarDecl(VarDecl *VD);
  virtual bool VisitCallExpr(CallExpr *CE);
  virtual bool VisitBinaryOperator(BinaryOperator *BO);
  virtual bool VisitUnaryOperator(UnaryOperator *UO);
  virtual bool VisitDeclRefExpr(DeclRefExpr *DRE);
  virtual bool VisitArraySubscriptExpr(ArraySubscriptExpr *ASE);
  virtual bool VisitDoStmt(DoStmt *DS);
  virtual bool VisitForStmt(ForStmt *FS);
  virtual bool VisitWhileStmt(WhileStmt *WS);
  virtual bool VisitIfStmt(IfStmt *IS);
  virtual bool VisitSwitchStmt(SwitchStmt *SS);
  virtual bool VisitOMPExecutableDirective(OMPExecutableDirective *S);

}; // end class OmpDartASTVisitor

#endif