{-# LANGUAGE DeriveFunctor #-}
module NormalForm where

import Names
import qualified PPrint as P

data Con' a
    = Var a
    | Star Sort
    | Pi a (Con' a) (NF' a)
    | Sigma a (Con' a) (NF' a)
    | Fin [String]
    | Lam a (NF' a)
    | Pair (Con' a) (Con' a)
    | Tag String
    deriving (Functor, Eq)

data NF' a
    = Con (Con' a)
    | Case a [(String, NF' a)]
    | App a (Con' a) (Con' a) (NF' a)
    | Proj a (Con' a) (Con' a) (NF' a)
    deriving (Functor, Eq)
type Con = Con' Ident

type NF = NF' Ident

type Type = NF

var :: a -> NF' a
var x = Con $ Var x

sort :: Sort -> NF' a
sort i = Con $ Star i

-- | Printing

instance P.Pretty a => P.Pretty (Con' a) where
    pretty a =
        case a of
          Var x -> P.pretty x
          Star s -> P.sort s
          Pi x c n -> P.piP x c $ P.pretty n
          Sigma x c n -> P.sigmaP x c $ P.pretty n
          Fin l -> P.finP l
          Lam x n -> P.lamP x $ P.pretty n
          Pair x y -> P.pairP x y
          Tag s -> P.text s

instance P.Pretty a => P.Pretty (NF' a) where
    pretty a =
        case a of
          Case x l -> P.caseP x $ map (\(s,t') -> (s, P.pretty t')) l
          App y f x n -> P.letP1 y (P.pretty f P.<+> P.pretty x) (P.pretty n)
          Proj x y z n -> P.letP2 x y (P.pretty z) (P.pretty n)
          Con x -> P.pretty x
