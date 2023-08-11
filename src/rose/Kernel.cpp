#include "Kernel.h"

using namespace clang;

Kernel::Kernel(const OMPExecutableDirective *TD, const FunctionDecl *FD) 
  : TD(TD), FD(FD) {}

const OMPExecutableDirective *Kernel::getDirective() const {
  return TD;
}

const FunctionDecl *Kernel::getFunction() const {
  return FD;
}

bool Kernel::contains(SourceLocation Loc) const {
  const CapturedStmt *CS = TD->getInnermostCapturedStmt();
  SourceLocation CSBeginLoc = CS->getBeginLoc();
  SourceLocation CSEndLoc = CS->getEndLoc();
  return (CSBeginLoc <= Loc) && (Loc < CSEndLoc);
}

SourceLocation Kernel::getBeginLoc() const {
  return TD->getInnermostCapturedStmt()->getBeginLoc();
}

SourceLocation Kernel::getEndLoc() const {
  return TD->getInnermostCapturedStmt()->getEndLoc();
}

int Kernel::recordPrivate(const ValueDecl *VD) {
  PrivateDecls.insert(VD);
  return 1;
}

const boost::container::flat_set<const ValueDecl *> &Kernel::getPrivateDecls() const {
  return PrivateDecls;
}

bool Kernel::isPrivate(const ValueDecl *VD) const {
  return PrivateDecls.contains(VD);
}

int Kernel::recordNestedDirective(const OMPExecutableDirective *TD) {
  NestedDirectives.push_back(TD);
  return 1;
}

void Kernel::print(llvm::raw_ostream &OS, const SourceManager &SM) const {
  OS << "\n|-- Function: " << FD->getNameAsString();
  OS << "\n|-- Location: ";
  TD->getBeginLoc().print(OS, SM);
  TD->getEndLoc().print(OS, SM);
  OS << "\n|   |-- InnermostCapturedStmt";
  OS << "\n|   |   |-- BeginLoc: ";
  TD->getInnermostCapturedStmt()->getBeginLoc().print(OS, SM);
  OS << "\n|   |   |-- EndLoc  : ";
  TD->getInnermostCapturedStmt()->getEndLoc().print(OS, SM);

  OS << "\n|-- Data";
  if (PrivateDecls.size())
    OS << "\n|   |-- private";
  for (const ValueDecl *VD : PrivateDecls) {
    OS << "\n|   |   |-- " << VD->getNameAsString() << " loc: ";
    VD->getLocation().print(OS, SM);
    OS << " id: " << VD->getID();
  }
  if (MapTo.size())
    OS << "\n|   |-- to";
  for (const ValueDecl *VD : MapTo) {
    OS << "\n|   |   |-- " << VD->getNameAsString() << " loc: ";
    VD->getLocation().print(OS, SM);
    OS << " id: " << VD->getID();
  }
  if (MapFrom.size())
    OS << "\n|   |-- from";
  for (const ValueDecl *VD : MapFrom) {
    OS << "\n|   |   |-- " << VD->getNameAsString() << " loc: ";
    VD->getLocation().print(OS, SM);
    OS << " id: " << VD->getID();
  }
  if (MapToFrom.size())
    OS << "\n|   |-- tofrom";
  for (const ValueDecl *VD : MapToFrom) {
    OS << "\n|   |   |-- " << VD->getNameAsString() << " loc: ";
    VD->getLocation().print(OS, SM);
    OS << " id: " << VD->getID();
  }
  if (MapAlloc.size())
    OS << "\n|   |-- alloc";
  for (const ValueDecl *VD : MapAlloc) {
    OS << "\n|   |   |-- " << VD->getNameAsString() << " loc: ";
    VD->getLocation().print(OS, SM);
    OS << " id: " << VD->getID();
  }
  OS << "\n";
  return;
}

const boost::container::flat_set<const ValueDecl *> &Kernel::getMapTo() const {
  return MapTo;
}
const boost::container::flat_set<const ValueDecl *> &Kernel::getMapFrom() const {
  return MapFrom;
}
const boost::container::flat_set<const ValueDecl *> &Kernel::getMapToFrom() const {
  return MapToFrom;
}
const boost::container::flat_set<const ValueDecl *> &Kernel::getMapAlloc() const {
  return MapAlloc;
}
