{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module RawSyntax where
import Language.LBNF

bnfc [lbnf|

comment "--" ;
comment "{-" "-}" ;

ETag.    Exp6 ::= "'" AIdent;
EFin.    Exp6 ::= OpenBrack [AIdent] "]";
ECas.    Exp6 ::= "using" AIdent "|" Exp "case" Exp "of" Open [Defin] "}" ;
EHole.   Exp6 ::= Hole ;
EVar.    Exp6 ::= AIdent ;
ESet.    Exp6 ::= Sort ;
EProj.   Exp4 ::= Exp4 "." AIdent ;
EApp.    Exp3 ::= Exp3 Exp4 ;
EPi.     Exp2  ::= Exp3 Arrow Exp2 ;
ESigma.  Exp2  ::= Open [Exp] "}" ;
EAbs.    Exp2  ::= "\\" [Bind] Arrow Exp2 ;
EThis.   Exp6  ::= "this" ;
EAnn.    Exp1 ::= Exp2 ":" Exp1 ;
EPair.   Exp  ::= [Defin] ;

coercions Exp 6 ;

separator Exp ";";


Def.   Defin ::= AIdent "=" Exp ;
separator nonempty Defin ",";
separator AIdent ",";

token Arrow  ('-' '>') ;

NoBind. Bind   ::= AIdent ; 
Bind.   Bind   ::= "(" AIdent ":" Exp ")" ;
AIdent. AIdent ::= Identifier ;
terminator Bind "" ;

token Natural digit+;

position token Open ('{');
position token OpenBrack ('[');
position token Identifier ('!'|letter|digit|'-'|'_')((letter|digit|'-'|'_'|'\'')*) ;
position token Hole '?' ((letter|digit|'-'|'_'|'\'')*) ;

position token Sort ('#' | '*' (digit*));

|]
