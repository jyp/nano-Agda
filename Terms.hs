module Terms where

import Names


type Position = (Int,Int)

type Ident = (Name,Position)


data Term' name ref

    = Var ref

    | Pi  name ref (T_loc name ref) (T_loc name ref) (T_loc name ref)   -- let z = Π(x:A) B = (x:A)→B in t
    | Lam name ref (T_loc name ref) (T_loc name ref) (T_loc name ref)   -- let z = λ(x:A).t in t'
    | App name ref ref (T_loc name ref)                                 -- let z = f x in t

    | Sigma name ref (T_loc name ref) (T_loc name ref) (T_loc name ref) -- let z = Σ(x:A) B = (x:A)×B in t
    | Pair  name ref ref                                                -- let z = (x,y) in t NOT SURE HERE
    | Proj  name ref ref (T_loc name ref)                               -- let (x,y) = z in t

    | Fin name [String] (T_loc name ref)                                -- let z = { 'tagᵢ | i = 1..n } in t
    | Tag String                                                        -- 'tagᵢ
    | Case ref [(String,(T_loc name ref))]                              -- case x do { 'tagᵢ → tᵢ | i = 1..n }

    deriving (Show)

type T_loc name ref = (Term' name ref, Position)

type Term = T_loc Ident Ident
