module Terms where

import Control.Arrow ((***))
import qualified PPrint as P

import Names

data TLoc' name ref

    = Var ref

    | Pi  name Sort name ref (TLoc name ref) (TLoc name ref)   -- let y : s = (x:ty)→T' in T
    | Lam name ref name (TLoc name ref) (TLoc name ref)       -- let y : ty = λx.T' in T
    | App name ref ref (TLoc name ref)                        -- let y = f x in T

    | Sigma name Sort name ref (TLoc name ref) (TLoc name ref) -- let y : s = (x:ty)×T' in T
    | Pair name ref ref ref (TLoc name ref)                  -- let z : ty = (x,y) in T
    | Proj name name ref (TLoc name ref)                     -- let (x,y) = z in T

    | Fin name [String] (TLoc name ref)                   -- let x = { 'tagᵢ / i = 1..k } in T
    | Tag name ref String (TLoc name ref)                     -- let x : ty = 'tagᵢ in T
    | Case ref [(String, TLoc name ref)]                      -- case x { 'tagᵢ → Tᵢ / i = 1..k }

    | Star Sort                                               -- *ᵢ

    deriving (Eq)

type TLoc name ref = (TLoc' name ref, Position)

type Term' = TLoc' Ident Ident
type Term = TLoc Ident Ident

var :: Ident -> Term
var i = (Var i, getPos i)

-- | Name manipulation

mapName :: (a -> b) -> TLoc a a -> TLoc b b
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
    f' (Star s)            = Star s

replaceName :: Ident -> Ident -> Term -> Term
replaceName name name' t = mapName replace t where
    replace n | n == name  = name'
              | otherwise = n

-- | Pretty

instance (P.Pretty a, P.Pretty b) => P.Pretty (TLoc' a b) where
    pretty t =
        case t of
          Var i -> P.pretty i

          Pi i s x tyA tyB t' ->
              P.letP (P.vartype i s) (P.piP x tyA $ P.pretty tyB) (P.pretty t')
          Lam i ty x tfun t' ->
              P.letP (P.vartype i ty) (P.lamP x $ P.pretty tfun) (P.pretty t')
          App i f x t' ->
              P.letP1 i (P.pretty f P.<+> P.pretty x) (P.pretty t')

          Sigma i s x tyA tyB t' ->
              P.letP (P.vartype i s) (P.sigmaP x tyA $ P.pretty tyB) (P.pretty t')
          Pair i ty x y t' ->
              P.letP (P.vartype i ty) (P.pairP x y) (P.pretty t')
          Proj i1 i2 z t' ->
              P.letP2 i1 i2 (P.pretty z) (P.pretty t')

          Fin i l t' ->
               P.letP1 i (P.finP l) (P.pretty t')
          Tag i ty s t' -> P.letP (P.vartype i ty) (P.text s) (P.pretty t')
          Case x l -> P.caseP x $ map (\(s,t') -> (s, P.pretty t')) l
          Star s -> P.sort s

instance (P.Pretty a, P.Pretty b) => P.Pretty (TLoc a b) where
    pretty (t,_) = P.pretty t
