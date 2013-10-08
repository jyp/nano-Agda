module Terms where

import Control.Arrow ((***))

import Names

data TLoc' name ref

    = Var ref

    | Pi  name Sort ref ref (TLoc name ref) (TLoc name ref)   -- let z : S = Π(x:A) B = (x:A)→B in t
    | Lam name ref ref (TLoc name ref) (TLoc name ref)   -- let z : T = λx.t in t'
    | App name ref ref (TLoc name ref)                   -- let z = f x in t

    | Sigma name Sort ref ref (TLoc name ref) (TLoc name ref) -- let z : S = Σ(x:A) B = (x:A)×B in t
    | Pair  name ref ref ref (TLoc name ref)             -- let z : T = (x,y) in t
    | Proj  name name ref (TLoc name ref)                -- let (x,y) = z in t

    | Fin name [String] (TLoc name ref)                  -- let z = { 'tagᵢ | i = 1..n } in t
    | Tag name ref String (TLoc name ref)                -- let z : T = 'tagᵢ in t
    | Case ref [(String, TLoc name ref)]                 -- case x do { 'tagᵢ → tᵢ | i = 1..n }

    | Star Sort                                          -- *ᵢ

    deriving (Show)

type TLoc name ref = (TLoc' name ref, Position)

type Term' = TLoc' Ident Ident
type Term = TLoc Ident Ident
