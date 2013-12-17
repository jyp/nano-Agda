module Env where

import Common

import Names
import PPrint
import qualified Text.PrettyPrint as P
import NormalForm(NF,Con,Type)
import qualified NormalForm as NF
import Data.Maybe(fromMaybe)
import Data.List(find)

import qualified Data.Map as M

data Definition
    = App Ident Con        -- y = f x
    | Lam Ident NF         -- f = λx.n
    | ITag String          -- x = 'tag
    | ETag String          -- x = 'tag
    | IPair Ident Ident    -- z = (x,y)
    | EPair Ident Ident    -- (x,y) = z
    | Alias Ident          -- z = z'
    | Pi Ident Ident NF    -- σ = (x:ty)→n
    | Sigma Ident Ident NF -- σ = (x:ty)×n
    | Fin [String]         -- σ = { 'bla, 'bli, 'blo }
    | Star Int             -- σ = *ᵢ
    | Def NF
    deriving (Eq)

instance Pretty Definition where
    pretty (App f x) = pretty f <+> pretty x
    pretty (Lam i t) = lamP i (pretty t)
    pretty (ITag x) = text x <> intro
    pretty (ETag x) = text x <> elim
    pretty (IPair x y) = pairP x y <> intro
    pretty (EPair x y) = pairP x y <> elim
    pretty (Alias x) = pretty x
    pretty (Pi x tyA tyB) = piP x tyA $ pretty tyB
    pretty (Sigma x tyA tyB) = sigmaP x tyA $ pretty tyB
    pretty (Fin l) = finP l
    pretty (Star i) = sort i
    pretty (Def t) = pretty t

type Context = M.Map Name Type
type EnvIntro = M.Map Name Definition
type EnvElim = M.Map Name [Definition]

data Env = Env Context EnvIntro EnvElim
    deriving (Eq)

(∪) :: Env -> Env -> Env
(Env c1 ei1 ee1) ∪ (Env c2 ei2 ee2) =
    let c = M.union c1 c2
        ei = M.union ei1 ei2
        ee = M.unionWith (++) ee1 ee2
    in Env c ei ee

instance Pretty Env where
    pretty (Env c ei _) =
        P.text "Context :" <+> pretty c $+$
        P.text "EnvIntro :" <+> pretty ei

instance Pretty (Env,Ident) where
    pretty (_,i) = P.text "<stuff," <+> pretty i <+> P.text ">"

instance Pretty (Env, [(Ident, Ident, Ident)]) where
    pretty (e,l) =
        pretty e $+$ (P.vcat $ map printdef l)
            where
              printdef (i,t,ty) =
                  pretty i
                  <+> P.colon <+> pretty ty
                  <+> P.equals <+> pretty t

mapName :: (Name -> Name) -> Env -> Env
mapName f (Env c ei ee) =
    let c'  = M.map (fmap (>~ f)) $ M.mapKeys f c
        ei' = M.map (mapNameDef f) $ M.mapKeys f ei
        ee' = M.map (map $ mapNameDef f) $ M.mapKeys f ee
    in Env c' ei' ee'

mapNameDef :: (Name -> Name) -> Definition -> Definition
mapNameDef mapN def =
    let m = (>~ mapN) in
    case def of
      App f x -> App (m f) (fmap m x)
      Lam i t -> Lam (m i) (fmap m t)
      ITag x -> ITag x
      ETag x -> ETag x
      IPair x y -> IPair (m x) (m y)
      EPair x y -> EPair (m x) (m y)
      Alias x -> Alias $ m x
      Pi x tyA t -> Pi (m x) (m tyA) $ (fmap m t)
      Sigma x tyA t -> Sigma (m x) (m tyA) $ (fmap m t)
      Fin l -> Fin l
      Star i -> Star i
      Def t -> Def (fmap m t)


empty :: Env
empty = Env M.empty M.empty M.empty

getType :: Env -> Ident -> NF
getType (Env c _ _) ident =
    case M.lookup (getN ident) c of
      Just t -> t
      Nothing ->
          error . show $
          text "Variable" <+> pretty ident <+>
          text "doesn't have a type."

getIntroOpt :: Env -> Ident -> Maybe Definition
getIntroOpt (Env _ e _) i =
    M.lookup (getN i) e

getIntro :: Env -> Ident -> Definition
getIntro e i =
    case getIntroOpt e i of
      Just t -> t
      Nothing ->
          error . show $
          text "Variable" <+> pretty i <+>
          text "doesn't have an introduction."

getElims :: Env -> Ident -> [Definition]
getElims (Env _ _ e) ident =
    case M.lookup (getN ident) e of
      Just t -> t
      Nothing ->
          error . show $
          text "Variable" <+> pretty ident <+>
          text "doesn't have any elimination."

getVal :: Env -> Ident -> Either Definition [Definition]
getVal e@(Env _ ei ee) i =
    case M.lookup (getN i) ei of
      Just (Alias x) -> getVal e x
      Just x -> Left x
      Nothing -> Right $ ee M.! (getN i)

addContext :: Env -> Ident -> NF -> Env
addContext (Env context ei ee) i ty =
    let context' = M.insert (getN i) ty context
    in Env context' ei ee

addIntro :: Env -> Ident -> Definition -> Env
addIntro (Env context ei ee) i t =
  let ei' = M.insert (getN i) t ei
  in Env context ei' ee

addBinding :: Env -> Ident -> Definition -> NF -> Env
addBinding env i t ty =
  let env' = addContext env i ty in
  addIntro env' i t

addElim :: Env -> Ident -> Definition -> Env
addElim (Env context ei ee) i t =
  let elims = fromMaybe [] $ M.lookup (getN i) ee
      ee' = M.insert (getN i) (t:elims) ee
  in Env context ei ee'

addAlias :: Env -> Ident -> Ident -> Env
addAlias env x y = do
  let ty = getType env y
  addBinding env x (Alias y) ty

-- | Verification functions

toNF :: Env -> Ident -> TypeError NF
toNF e i = do
  def <- e ! i
  case def of
    Lam x n -> retcon $ NF.Lam x n
    ITag x -> retcon $ NF.Tag x
    ETag x -> retcon $ NF.Tag x
    IPair x y -> retcon $ NF.Pair (NF.Var x) (NF.Var y)
    EPair x y -> retcon $ NF.Pair (NF.Var x) (NF.Var y)
    Pi x tyA t -> retcon $ NF.Pi x (NF.Var tyA) t
    Sigma x tyA t -> retcon $ NF.Sigma x (NF.Var tyA) t
    Fin l -> retcon $ NF.Fin l
    Star s -> retcon $ NF.Star s
    App f x -> return $ NF.App i f x (NF.var i)
    Alias x -> toNF e x
    Def t -> return t
    where retcon = return . NF.Con

(!) :: Env -> Ident -> TypeError Definition
env@(Env _ e _) ! ident =
    case M.lookup (getN ident) e of
      Just (Alias x) -> env ! x
      Just d -> return d
      Nothing -> throwError $ Abstract ident

infix 9 !

-- Check if i == i', modulo Aliases
areEqual :: Env -> Ident -> Ident -> Bool
areEqual env@(Env _ e _) ident ident' =
    ident == ident' ||
    case (M.lookup (getN ident) e , M.lookup (getN ident') e) of
      (Just (Alias a), Nothing) -> areEqual env a ident'
      (Nothing, Just (Alias a')) -> areEqual env ident a'
      (Just (Alias a), Just (Alias a')) -> areEqual env a a'
      (_ , _) -> False

-- | Normalization

normalize :: Env -> NF -> TypeError Con
normalize e n =
  case n of
    NF.Con (NF.Var x) -> do
        dx <- toNF e x
        normalize e dx
    NF.Con c -> return c
    NF.App _ f _ _ -> throwError $ Abstract f
    NF.Case x _ -> throwError $ Abstract x
    NF.Proj _ _ z _ -> throwError $ Abstract z
    -- Todo : reduce when we can.

normalizeSort :: Env -> NF -> TypeError Sort
normalizeSort env i = do
  con <- normalize env i
  case con of
    NF.Star s -> return s
    _ -> throwError $ Normalize i "Expected Sort."

normalizePi :: Env -> NF -> TypeError (Ident, Con, NF)
normalizePi env i = do
  con <- normalize env i
  case con of
    NF.Pi x tyA tyB -> return (x,tyA,tyB)
    _ -> throwError $ Normalize i "Expected Pi."

normalizeSigma :: Env -> NF -> TypeError (Ident, Con, NF)
normalizeSigma env i = do
  con <- normalize env i
  case con of
    NF.Sigma x tyA tyB -> return (x,tyA,tyB)
    _ -> throwError $ Normalize i "Expected Sigma."

normalizeFin :: Env -> NF -> TypeError [String]
normalizeFin env i = do
  con <- normalize env i
  case con of
    NF.Fin l -> return l
    _ -> throwError $ Normalize i "Expected Fin."

normalizeLam :: Env -> NF -> TypeError (Ident, NF)
normalizeLam env i = do
  con <- normalize env i
  case con of
    NF.Lam x t -> return (x,t)
    _ -> throwError $ Normalize i "Expected Lambda."

-- | Eliminator introduction

-- Case i
elimTag :: Env -> Ident -> String -> Env
elimTag env i s =
  addElim env i (ETag s)

-- Proj (x,y) = z
elimProj :: Env -> Ident -> Ident -> Ident -> NF -> NF -> Env
elimProj e x y z tyA tyB =
  case Env.getIntroOpt e z of
    Just (Env.IPair x' y') -> do
      let e_x = Env.addAlias e x' x
      Env.addAlias e_x y' y
    _ -> do
      let e_z = Env.addElim e z (Env.EPair x y)
          e_zx = Env.addContext e_z x tyA
      Env.addContext e_zx y tyB

-- App y = f x
elimApp :: Env -> Ident -> Ident -> Con -> NF -> Env
elimApp e y f x ty =
  case Env.getIntroOpt e f of
    Just (Env.Lam fx ft) -> do
      let ft_x = NF.subs' ft fx x
      Env.addBinding e y (Env.Def ft_x) ty
    _ -> do
      Env.addBinding e y (Env.App f x) ty
