{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module RawSyntax where
import Language.LBNF

bnfc [lbnf|

comment "--" ;
comment "{-" "-}" ;

EHole.   Exp6 ::= Hole ;
EVar.    Exp6 ::= AIdent ;
ESet.    Exp6 ::= Sort ;
EProj.   Exp4 ::= Exp4 "." AIdent ;
EExtr.   Exp4 ::= Exp4 "/" AIdent ;
EApp.    Exp3 ::= Exp3 Exp4 ;
EPi.     Exp2  ::= Exp3 Arrow Exp2 ;
ESigma.  Exp2  ::= Exp3 ";" Exp2 ;
EAbs.    Exp2  ::= "\\" [Bind] Arrow Exp2 ;
EAnn.    Exp1 ::= Exp2 ":" Exp1 ;
EPair.   Exp  ::= Decl "," Exp ;

coercions Exp 6 ;

Decl. Decl ::= AIdent "=" Exp1 ;
terminator AIdent "" ;

token Arrow  ('-' '>') ;

NoBind. Bind   ::= AIdent ; 
Bind.   Bind   ::= "(" AIdent ":" Exp ")" ;
AIdent. AIdent ::= Identifier ;
terminator Bind "" ;

token Natural digit+;

position token Identifier ('!'|'['|']'|letter|digit|'-'|'_'|'\'')(('*'|'['|']'|letter|digit|'-'|'_'|'\'')*) ;
position token Hole '?' ((letter|digit|'-'|'_'|'\'')*) ;

position token Sort ('#' | '*' (digit*));

|]
