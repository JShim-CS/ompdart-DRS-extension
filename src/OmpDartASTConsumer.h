#ifndef ROSEASTCONSUMER_H
#define ROSEASTCONSUMER_H

#include "clang/Rewrite/Core/Rewriter.h"

#include "OmpDartASTVisitor.h"
#include <unordered_map>

using namespace clang;

class OmpDartASTConsumer : public ASTConsumer {
  ASTContext *Context;
  SourceManager *SM;
  OmpDartASTVisitor *Visitor;
  Rewriter TheRewriter;
  std::string OutFilePath;
  bool Aggressive;
  unsigned *drdPragmaLineNumber;
  


  std::vector<DataTracker *> &FunctionTrackers;
  std::vector<Kernel *> &Kernels;

  
  std::unordered_map<std::string, bool> readMap;
  std::unordered_map<std::string, bool> writeMap;

public:
  explicit OmpDartASTConsumer(CompilerInstance *CI,
                              const std::string *OutFilePath, bool Aggressive, unsigned* drdPragmaLine);

  virtual void HandleTranslationUnit(ASTContext &Context);

private:
  CompilerInstance *CI;
  std::string getConditionOfLoop(ForStmt &FS, std::string &indexV);
  void recordReadAndWrite();
  std::string setStringForRegion(const Expr *exp, int *v, const std::string &indexV);
  std::string recursivelySetTheString(const Expr *exp, int *v, const std::string &indexV);
  void setArrayIndexEncoding(const Stmt *exp, int *v, const std::string &indexV, const std::string controlCondition, bool isWrite);
  std::string recursivelyFindArrayIndex(const Expr *exp, int *v, const std::string &indexV);
}; // end class OmpDartASTConsumer

#endif
