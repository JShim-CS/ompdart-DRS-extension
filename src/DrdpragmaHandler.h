#ifndef DRDPRAGMAHANDLER_H
#define DRDPRAGMAHANDLER_H

// #include "clang/Basic/SourceLocation.h"
// #include "clang/Lex/Pragma.h"
// #include "clang/Lex/Token.h"
// #include "clang/Lex/Preprocessor.h"

#include "clang/Basic/Diagnostic.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/Pragma.h"
#include <fstream>

#include <stdlib.h>

using namespace clang;

class DrdpragmaHandler : public PragmaHandler {
public:
    SourceLocation drd_sl; //for handling pragma later on
    bool found;
    unsigned *lineNumber;
    DrdpragmaHandler() : PragmaHandler("drd"), found(false) {}

    //written by Junhyung Shim
    //gets the line-number of a #pragma 
    void HandlePragma(Preprocessor &PP, PragmaIntroducer Introducer, Token &Token) override{
        if(found){
            //cannot use diagnostics here
            llvm::outs() << "Error: Only 1 #pragma drd allowed! (exiting program)\n";
            exit(0);
        }
        this->drd_sl = Token.getLocation(); 
        SourceManager &SM = PP.getSourceManager();
        unsigned pragmaLine = SM.getSpellingLineNumber(Token.getLocation());
        *lineNumber = pragmaLine;
        llvm::outs() << "Encountered #pragma drd on line: " << *lineNumber << "\n";
        this->found = true;
        
        std::ofstream pragLineFile("/programming/ompdart/PRAGMA_LINE_NUMBER.txt");
        if (!pragLineFile.is_open()) {
            llvm::outs() << "ERROR at <DrdpragmaHandler.h> quitting program .\n";
            exit(0);
        }
        pragLineFile << pragmaLine << std::endl;
        pragLineFile.close();

        PP.Lex(Token);
    }

};




#endif