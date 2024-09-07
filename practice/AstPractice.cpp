#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

SourceManager *sm;
CompilerInstance *ci;

class FindNamedClassVisitor
  : public RecursiveASTVisitor<FindNamedClassVisitor> {
public:  
  explicit FindNamedClassVisitor(ASTContext *Context)
    : Context(Context) {}
  
  bool VisitCXXRecordDecl(CXXRecordDecl *Declaration) {
    if (Declaration->getQualifiedNameAsString() == "n::m::C") {
      FullSourceLoc FullLocation = Context->getFullLoc(Declaration->getBeginLoc());
      if (FullLocation.isValid())
        llvm::outs() << "Found declaration at "
                     << FullLocation.getSpellingLineNumber() << ":"
                     << FullLocation.getSpellingColumnNumber() << "\n";
    }
    return true;
  }

  bool VisitIfStmt(IfStmt *s){
    Expr *expr = s->getCond();
    SourceLocation startLocation = expr->getBeginLoc();
    SourceLocation endLocation = expr->getEndLoc();
    CharSourceRange conditionRange = CharSourceRange::getTokenRange(startLocation,endLocation);
    bool invalid;
    StringRef str = Lexer::getSourceText(conditionRange,*sm, (*ci).getLangOpts(),&invalid);
    if(invalid)return false;
    llvm::outs() << "Condition: " << str << "\n";
    return true;
  }

private:
  ASTContext *Context;
};

class FindNamedClassConsumer : public clang::ASTConsumer {
public:
  explicit FindNamedClassConsumer(ASTContext *Context)
    : Visitor(Context) {}

  virtual void HandleTranslationUnit(clang::ASTContext &Context) {
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());
  }
private:
  FindNamedClassVisitor Visitor;
};

class FindNamedClassAction : public clang::ASTFrontendAction {
public:
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
    clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    SourceManager &s = Compiler.getASTContext().getSourceManager();
    clang::CompilerInstance &c = Compiler;
    sm = &s;
    ci = &c;

    return std::make_unique<FindNamedClassConsumer>(&Compiler.getASTContext());
  }
};

int main(int argc, char **argv) {
  if (argc > 1) {
    clang::tooling::runToolOnCode(std::make_unique<FindNamedClassAction>(), argv[1]);
  }
}