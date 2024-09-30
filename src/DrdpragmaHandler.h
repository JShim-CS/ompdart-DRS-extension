#ifndef DRDPRAGMAHANDLER_H
#define DRDPRAGMAHANDLER_H

// #include "clang/Basic/SourceLocation.h"
// #include "clang/Lex/Pragma.h"
// #include "clang/Lex/Token.h"
// #include "clang/Lex/Preprocessor.h"

#include "clang/Basic/Diagnostic.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Pragma.h"


using namespace clang;

class DrdpragmaHandler : public PragmaHandler {
public:
    SourceLocation drd_sl; //for handling pragma later on
    bool found;
    unsigned *lineNumber;
    DrdpragmaHandler() : PragmaHandler("drd"), found(false) {}

    //written by Junhyung Shim
    //sets the line-number of a #pragma 
    void HandlePragma(Preprocessor &PP, PragmaIntroducer Introducer, Token &Token) override;

};




#endif