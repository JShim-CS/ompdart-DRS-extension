#ifndef ROSEASTCONSUMER_H
#define ROSEASTCONSUMER_H

#include "clang/Rewrite/Core/Rewriter.h"

#include "OmpDartASTVisitor.h"
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

public:
  explicit OmpDartASTConsumer(CompilerInstance *CI,
                              const std::string *OutFilePath, bool Aggressive, unsigned* drdPragmaLine);

  virtual void HandleTranslationUnit(ASTContext &Context);

private:
  CompilerInstance *CI;
  std::string getConditionOfLoop(ForStmt &FS, std::string &indexV);
  void recordReadAndWrite();
  std::string setStringForRegion(const Expr *exp, int v, const std::string &indexV,std::vector<std::string> &indexEncodings);
  std::string recursivelySetTheString(const Expr *exp, int v, const std::string &indexV,std::vector<std::string> &indexEncodings);

}; // end class OmpDartASTConsumer

#endif
