module Terms where

import Control.Arrow ((***))

import Names

data TLoc' name ref

    = Var ref

    | Pi  name Sort name ref (TLoc name ref) (TLoc name ref)   -- let i : S = Π(x:A) B = (x:A)→<B> in <t>
    | Lam name ref name (TLoc name ref) (TLoc name ref)   -- let i : S = λx.<t'> in <t>
    | App name ref ref (TLoc name ref)                   -- let i = f x in <t>

    | Sigma name Sort name ref (TLoc name ref) (TLoc name ref) -- let i : S = Σ(x:A) B = (x:A)×B in t
    | Pair  name ref ref ref (TLoc name ref)             -- let i : S = (x,y) in <t>
    | Proj  name name ref (TLoc name ref)                -- let (x,y) = z in <t>

    | Fin name [String] (TLoc name ref)                  -- let i = { 'tagᵢ | i = 1..n } in <t>
    | Tag name ref String (TLoc name ref)                -- let i : T = 'tagᵢ in <t>
    | Case ref [(String, TLoc name ref)]                 -- case x do { 'tagᵢ → <tᵢ> | i = 1..n }

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
    f' (Pi i s x tyA tyB t)    = Pi (f i) s (f x) (f tyA) (mapName f tyB) (mapName f t)
    f' (Lam i ty x tf t)       = Lam (f i) (f ty) (f x) (mapName f tf) (mapName f t)
    f' (App i xf x t)          = App (f i) (f xf) (f x) (mapName f t)
    f' (Sigma i s x tyA tyB t) = Sigma (f i) s (f x) (f tyA) (mapName f tyB) (mapName f t)
    f' (Pair i ty x y t)       = Pair (f i) (f ty) (f x) (f y) (mapName f t)
    f' (Proj x y z t)          = Proj (f x) (f y) (f z) (mapName f t)
    f' (Fin i l t)             = Fin (f i) l (mapName f t)
    f' (Tag i ty tag t)        = Tag (f i) (f ty) tag (mapName f t)
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
