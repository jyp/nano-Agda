{
module Lexer where
}

%wrapper "posn"

$special = [\→\*\×\\\λ\(\{\}\)\,\:\.]
$graphic = $printable # $white
$allowedchar = $graphic # $special
$digit = 0-9
@ident = ( $allowedchar # \')$allowedchar*
@tag = "'" $allowedchar+

:-
"--".* ; -- Toss single line comments
$white+ ;

let        { constPT T_Let }
case       { constPT T_Case }
in         { constPT T_In }
"\\" | "λ" { constPT T_Lambda }
"->" | "→" { constPT T_To }
"*"        { constPT T_Star }
"×"        { constPT T_Cross }
"("        { constPT T_PARL }
")"        { constPT T_PARR }
"{"        { constPT T_ACCL }
"}"        { constPT T_ACCR }
","        { constPT T_COMMA }
"."        { constPT T_DOT }
"::"       { constPT T_2COLON }
":"        { constPT T_COLON }
"="        { constPT T_EQUAL }
$digit+    { varPT $ T_Int . read }
@tag       { varPT T_Tag }
@ident     { varPT T_Ident }

{

data Tok
 = T_Let
 | T_Case
 | T_In
 | T_Lambda
 | T_To
 | T_Cross | T_Star
 | T_PARL | T_PARR
 | T_ACCL | T_ACCR
 | T_COMMA | T_DOT
 | T_COLON | T_2COLON | T_EQUAL
 | T_Tag !String
 | T_Ident !String
 | T_Int !Int

 deriving (Eq,Show,Ord)

data Token =
   PT  (Int,Int,Int) Tok
 | Err (Int,Int,Int)
  deriving (Eq,Show)


getPos :: AlexPosn -> (Int,Int,Int)
getPos (AlexPn x y z) = (x,y,z)

constPT :: Tok -> AlexPosn -> String -> Token
constPT tok pos s = PT (getPos pos) tok

varPT :: (String -> Tok) -> AlexPosn -> String -> Token
varPT tok pos s = PT (getPos pos) (tok s)

tokenPosn (PT p _) = p
tokenPosn (Err p) = p

}
