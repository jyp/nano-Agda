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

    deriving (Show, Eq)

type TLoc name ref = (TLoc' name ref, Position)

type Term' = TLoc' Ident Ident
type Term = TLoc Ident Ident

type Type = Term

-- | Name manipulation

mapName :: (Ident -> Ident) -> Term -> Term
mapName f = f' *** id where
    f' (Var n)                 = Var $ f n
    f' (Pi z s x tyA tyB t)    = Pi (f z) s (f x) (f tyA) (mapName f tyB) (mapName f t)
    f' (Lam z ty x tf t)       = Lam (f z) (f ty) (f x) (mapName f tf) (mapName f t)
    f' (App z xf x t)          = App (f z) (f xf) (f x) (mapName f t)
    f' (Sigma z s x tyA tyB t) = Sigma (f z) s (f x) (f tyA) (mapName f tyB) (mapName f t)
    f' (Pair z ty x y t)       = Pair (f z) (f ty) (f x) (f y) (mapName f t)
    f' (Proj x y z t)          = Proj (f x) (f y) (f z) (mapName f t)
    f' (Fin z l t)             = Fin (f z) l (mapName f t)
    f' (Tag z ty tag t)        = Tag (f z) (f ty) tag (mapName f t)
    f' (Case x l)              = Case (f x) (map (id *** mapName f) l)
    f' (Star i)                = Star i

replaceName :: Ident -> Ident -> Term -> Term
replaceName name name' t = mapName replace t where
    replace n | n == name  = name'
              | otherwise = n

-- | Sort

type Sort = Int

above (Star i,pos) = (Star (i + 1), pos)

below (Star i, pos) = (Star (i - 1), pos)
