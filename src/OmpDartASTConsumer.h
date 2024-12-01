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

  //std::unordered_map<std::string, std::vector<std::string>> encodedIndexInfo;
  std::unordered_map<std::string, bool> readMap;
  std::unordered_map<std::string, bool> writeMap;
  std::unordered_map<std::string,bool> encodedWriteOrRead; //true if used for write op
  std::unordered_map<std::string,short> diffRequiredMap;
public:
  explicit OmpDartASTConsumer(CompilerInstance *CI,
                              const std::string *OutFilePath, bool Aggressive, unsigned* drdPragmaLine, std::unordered_map<std::string, std::string> *macros);

  virtual void HandleTranslationUnit(ASTContext &Context);

private:
  CompilerInstance *CI;
  std::string getConditionOfLoop(ForStmt &FS, std::string indexVar, std::unordered_map<std::string,short> &indexV, short diff);
  //std::string getConditionOfLoopWithoutRecording(ForStmt &FS, std::string indexVar);
  void recordReadAndWrite();
  std::string replaceTildeWithNum(std::string stringToChange, int num);
  std::string setStringForRegion(const Expr *exp, int *v, std::unordered_map<std::string, short> &indexV);
  std::string recursivelySetTheString(const Expr *exp, int *v, std::unordered_map<std::string, short> &indexV);
  std::string getLoopVariable(const ForStmt *exp);
  void setArrayIndexEncoding(const Stmt *exp, int *v, std::unordered_map<std::string, short> &indexV, const std::string controlCondition, bool isWrite, std::unordered_map<std::string,std::string> &Encoded2Original);
  std::string recursivelyFindArrayIndex(const Expr *exp, int *v, std::unordered_map<std::string, short> &indexV);
  std::string getArrayNameAndIndices(const ArraySubscriptExpr *arrayExpr, int *v, std::unordered_map<std::string, short> &indexV);
  void separateStringBy(std::string st, char sep, std::vector<std::string> &vect);
  bool isSingleVar(std::string condition);
}; // end class OmpDartASTConsumer

#endif
