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
  std::unordered_map<std::string, std::string> *macros;


  std::vector<DataTracker *> &FunctionTrackers;
  std::vector<Kernel *> &Kernels;

  
  std::unordered_map<std::string, bool> readMap;
  std::unordered_map<std::string, bool> writeMap;
  std::unordered_map<std::string,bool> encodedWriteOrRead; //true if used for write op
public:
  explicit OmpDartASTConsumer(CompilerInstance *CI,
                              const std::string *OutFilePath, bool Aggressive, unsigned* drdPragmaLine, std::unordered_map<std::string, std::string> *macros);

  virtual void HandleTranslationUnit(ASTContext &Context);

private:
  CompilerInstance *CI;
  std::string getConditionOfLoop(ForStmt &FS, std::string indexVar, std::unordered_map<std::string,bool> &indexV);
  void recordReadAndWrite();
  std::string setStringForRegion(const Expr *exp, int *v, std::unordered_map<std::string, bool> &indexV);
  std::string recursivelySetTheString(const Expr *exp, int *v, std::unordered_map<std::string, bool> &indexV);
  std::string getLoopVariable(const ForStmt *exp);
  void setArrayIndexEncoding(const Stmt *exp, int *v, std::unordered_map<std::string, bool> &indexV, const std::string controlCondition, bool isWrite, std::unordered_map<std::string,std::string> &Encoded2Original);
  std::string recursivelyFindArrayIndex(const Expr *exp, int *v, std::unordered_map<std::string, bool> &indexV);
}; // end class OmpDartASTConsumer

#endif
