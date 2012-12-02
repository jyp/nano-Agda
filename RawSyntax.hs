{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module RawSyntax where
import Language.LBNF

bnfc [lbnf|

comment "--" ;
comment "{-" "-}" ;

EThis.   Exp6 ::= "this" ;
ETag.    Exp6 ::= "'" AIdent;
EFin.    Exp6 ::= "[" [AIdent] "]";
EHole.   Exp6 ::= Hole ;
EVar.    Exp6 ::= AIdent ;
ESet.    Exp6 ::= Sort ;
ECas.    Exp4 ::= "case" AIdent "of" "{" [Defin] "}" ;
ESplit.  Exp4 ::= "split" AIdent "into" [AIdent] "in" Exp4 ;
EApp.    Exp4 ::= "with" AIdent "=" AIdent [Exp5] "in" Exp4 ;
EPi.     Exp2 ::= Exp3 Arrow Exp2 ;
ESigma.  Exp2 ::= "{" [Exp] "}" ;
EAbs.    Exp2 ::= "\\" [Bind] Arrow Exp2 ;
EAnn.    Exp1 ::= Exp2 ":" Exp1 ;
EPair.   Exp  ::= [Defin] ;


coercions Exp 6 ;

separator Exp ";";
terminator Exp5 "";

Def.   Defin ::= AIdent "=" Exp ;
separator nonempty Defin ",";
separator AIdent ",";

token Arrow  ('-' '>') ;

NoBind. Bind   ::= AIdent ; 
Bind.   Bind   ::= "(" AIdent ":" Exp ")" ;
AIdent. AIdent ::= Identifier ;
terminator Bind "" ;

token Natural digit+;

position token Identifier ('!'|letter|digit|'-'|'_')((letter|digit|'-'|'_'|'\'')*) ;
position token Hole '?' ((letter|digit|'-'|'_'|'\'')*) ;

position token Sort ('#' | '*' (digit*));

|]
