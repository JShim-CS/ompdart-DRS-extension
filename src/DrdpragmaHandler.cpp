#include "DrdpragmaHandler.h"

void DrdpragmaHandler::HandlePragma(Preprocessor &PP, PragmaIntroducer Introducer, Token &Token){
    if(this->found){
        //cannot use diagnostics here
        llvm::outs() << "Error: Only 1 #pragma drd allowed! (exiting program)\n";
        exit(0);
    }
    this->drd_sl = Token.getLocation(); 
    SourceManager &SM = PP.getSourceManager();
    unsigned pragmaLine = SM.getSpellingLineNumber(Token.getLocation());
    *lineNumber = pragmaLine;
    llvm::outs() << "Encountered #pragma drs on line: " << *lineNumber << "\n";
    this->found = true;
    PP.Lex(Token);
}


