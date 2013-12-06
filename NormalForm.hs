{-# LANGUAGE DeriveFunctor, DeriveFoldable #-}
module NormalForm where

import Data.Foldable
import qualified Data.Maybe as Maybe
import qualified Data.List as List

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
    deriving (Functor, Foldable, Eq)

data NF' a
    = Con (Con' a)
    | Case a [(String, NF' a)]
    | App a a (Con' a) (NF' a)
    | Proj a a a (NF' a)
    deriving (Functor, Foldable, Eq)

type Con = Con' Ident

type NF = NF' Ident

type Type = NF

var :: a -> NF' a
var x = Con $ Var x

sort :: Sort -> NF' a
sort i = Con $ Star i

-- | Substitution

-- We may be able to do better with some Traversable/Foldable magic.

subs :: NF -> Ident -> NF -> NF
subs t i (Case x l) =
  Case x (map (\(tag,n) -> (tag, subs t i n)) l)
subs t i (App y f x n) =
  App y f x (subs t i n)
subs t i (Proj x y z n) =
  Proj x y z (subs t i n)
subs t i (Con c) =
  subs' t i c

subs' :: NF -> Ident -> Con -> NF

subs' (Case x l) i c@(Tag tag) | i == x =
  let branch = Maybe.fromJust $ List.lookup tag l in
  subs' branch i c
subs' (Case x l) i s@(Var x') | i == x =
  Case x' (map f l)
       where
         f (tag,n) = (tag, subs' n i s)
subs' (Case x l) i s =
  Case x (map f l)
       where
         f (tag,n) = (tag, subs' n i s)

subs' (App y f x n) i c@(Lam a nf) | i == f =
  let x'   = subsC x  f c
      nf_y = subs' nf a x'
      n'   = subs  n  y nf_y in
  subs' n' f c
subs' (App y _f x n) i c@(Var f') =
    App y f' (subsC x i c) (subs' n i c)
subs' (App y f x n) i c =
    App y f (subsC x i c) (subs' n i c)

subs' (Proj x y z n) i c@(Pair x' y') | i == z =
  let n_x = subs' n   x x'
      n_y = subs' n_x y y' in
  subs' n_y i c
subs' (Proj x y _z n) i c@(Var z') =
    Proj x y z' (subs' n i c)
subs' (Proj x y z n) i c =
    Proj x y z (subs' n i c)
subs' (Con c) i s = Con (subsC c i s)

subsC :: Con -> Ident -> Con -> Con
subsC (Var x) i s | x == i = s
subsC (Pi x c n) i s = Pi x (subsC c i s) (subs' n i s)
subsC (Sigma x c n) i s = Sigma x (subsC c i s) (subs' n i s)
subsC (Lam x n) i s = Lam x (subs' n i s)
subsC (Pair c1 c2) i s = Pair (subsC c1 i s) (subsC c2 i s)
subsC c@(Var _) _ _ = c
subsC c@(Fin _) _ _ = c
subsC c@(Star _) _ _ = c
subsC c@(Tag _) _ _ = c

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
