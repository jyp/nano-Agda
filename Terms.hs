module Terms where

import Names

data Term' name ref

    = Var ref

    | Pi  name ref (TLoc name ref) (TLoc name ref) (TLoc name ref)   -- let z = Π(x:A) B = (x:A)→B in t
    | Lam name ref (TLoc name ref) (TLoc name ref) (TLoc name ref)   -- let z = λ(x:A).t in t'
    | App name ref ref (TLoc name ref)                               -- let z = f x in t

    | Sigma name ref (TLoc name ref) (TLoc name ref) (TLoc name ref) -- let z = Σ(x:A) B = (x:A)×B in t
    | Pair  name ref ref (TLoc name ref)                             -- let z = (x,y) in t
    | Proj  name name ref (TLoc name ref)                            -- let (x,y) = z in t

    | Fin name [String] (TLoc name ref)                              -- let z = { 'tagᵢ | i = 1..n } in t
    | Tag String                                                     -- 'tagᵢ
    | Case ref [(String, TLoc name ref)]                             -- case x do { 'tagᵢ → tᵢ | i = 1..n }

    deriving (Show)

type TLoc name ref = (Term' name ref, Position)

type Term = TLoc Ident Ident
