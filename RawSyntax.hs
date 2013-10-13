module RawSyntax where

import Common
import qualified Terms as T
import qualified Names as N

import Data.List(sortBy,groupBy)
import Data.Ord(comparing)

-- | The abstract syntax tree.

type Position = (Int,Int,Int)

pointPos :: Position -> N.Position
pointPos (_,l,c) = N.Point l c

rangePos :: Position -> Position -> N.Position
rangePos (_,l1,c1) (_,l2,c2) = N.Range l1 c1 l2 c2

newtype Tag = TTag (Position,String) deriving (Eq,Ord,Show)
newtype Ident = Ident (Position,String) deriving (Eq,Ord,Show)

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

-- | Main translation function

toTerm :: (Ident,Term) -> N.EnvM (N.Ident, T.Term)
toTerm = undefined


-- | Utility translation functions

smtToTerm :: (Ident,Term,Term) -> (N.Ident, T.Term, T.Type)
smtToTerm (i, t, ty)=
    let itt = do
          (i', ty') <- toTerm (i, ty)
          (_, t') <- toTerm (i, t)
          return (i', t', ty')
    in
      N.runEnv itt

getIdent :: Smt -> Ident
getIdent (TypDec i _ ) = i
getIdent (Def i _ ) = i

groupSmt :: [Smt] -> Err [(Ident,Term,Term)]
groupSmt decs =
    let decsSort = sortBy (comparing getIdent) decs
        decsGroup = groupBy (\x y -> getIdent x == getIdent y) decsSort
    in mapM f decsGroup where
        f [ TypDec i ty , Def _ t ] = return (i,t,ty)
        f [ Def i t , TypDec _ ty ] = return (i,t,ty)
        f [ Def i _ ] =
            throw $ "Definition of " ++ show i ++ " lacks a type declaration."
        f [ TypDec i _ ] =
            throw $ "Type declaration of " ++ show i ++ " lacks a definition."
        f (h:_) =
            throw $ show (getIdent h) ++ " has multiple definitions or declarations."
        f [] = undefined


convertFile :: [Smt] -> Err [(N.Ident,T.Term,T.Type)]
convertFile l = do
  decs <- groupSmt l
  return (map smtToTerm decs)
