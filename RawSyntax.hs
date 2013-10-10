module RawSyntax where

import qualified Terms as T
import qualified Names as N

type Position = (Int,Int,Int)

data Tag = TTag Position String deriving (Eq,Ord,Show)
data Ident = Ident Position String deriving (Eq,Ord,Show)

data Smt =
   TypDec Ident Term
 | Def Ident Term
  deriving (Eq,Ord,Show)

type VarType = (Ident, Ident)

type Pair = (Ident, Ident)

data Term =
   Var   Ident
 | Pi    Position Ident Ident VarType Term Position Term
 | Lam   Position Ident Ident Ident Term   Position Term
 | App   Position Ident Ident Ident        Position Term
 | Sigma Position Ident Ident VarType Term Position Term
 | Pair  Position Ident Ident Pair         Position Term
 | Proj  Position Pair Ident               Position Term
 | Fin   Position Ident [Tag]              Position Term
 | Tag   Position Ident Ident Tag          Position Term
 | Case  Position Ident [CaseCont]
 | Star  Int
  deriving (Eq,Ord,Show)

data CaseCont = CaseCont Tag Term
  deriving (Eq,Ord,Show)

convert :: (Ident,Term) -> (N.Ident,T.Term)
convert = undefined

groupSmt :: [Smt] -> [(Ident,Term,Term)]
groupSmt = undefined

convertFile :: [Smt] -> [(N.Ident,T.Term,T.Type)]
convertFile l = map f $ groupSmt l where
    f _ = undefined
