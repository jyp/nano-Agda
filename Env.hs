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
    = App Ident Ident      -- y = f x
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
      App f x -> App (m f) (m x)
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


empty :: Env
empty = Env M.empty M.empty M.empty

getType :: Env -> Ident -> NF
getType (Env c _ _) ident@(i,_,_) =
    case M.lookup i c of
      Just t -> t
      Nothing ->
          error . show $
          text "Variable" <+> pretty ident <+>
          text "doesn't have a type."

getIntro :: Env -> Ident -> Definition
getIntro (Env _ e _) ident@(i,_,_) =
    case M.lookup i e of
      Just t -> t
      Nothing ->
          error . show $
          text "Variable" <+> pretty ident <+>
          text "doesn't have an introduction."

getElims :: Env -> Ident -> [Definition]
getElims (Env _ _ e) ident@(i,_,_) =
    case M.lookup i e of
      Just t -> t
      Nothing ->
          error . show $
          text "Variable" <+> pretty ident <+>
          text "doesn't have any elimination."

getVal :: Env -> Ident -> Either Definition [Definition]
getVal e@(Env _ ei ee) (i,_,_) =
    case M.lookup i ei of
      Just (Alias x) -> getVal e x
      Just x -> Left x
      Nothing -> Right $ ee M.! i

addContext :: Env -> Ident -> NF -> Env
addContext (Env context ei ee) (i,_,_) ty =
    let context' = M.insert i ty context
    in Env context' ei ee

addIntro :: Env -> Ident -> Definition -> Env
addIntro (Env context ei ee) (i,_,_) t =
  let ei' = M.insert i t ei
  in Env context ei' ee

addBinding :: Env -> Ident -> Definition -> NF -> Env
addBinding env i t ty =
  let env' = addContext env i ty in
  addIntro env' i t

addElim :: Env -> Ident -> Definition -> Env
addElim (Env context ei ee) (i,_,_) t =
  let elims = fromMaybe [] $ M.lookup i ee
      ee' = M.insert i (t:elims) ee
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
    App f x -> return $ NF.App i (NF.Var f) (NF.Var x) (NF.Con $ NF.Var i)
    Alias x -> toNF e x
    where retcon = return . NF.Con

(!) :: Env -> Ident -> TypeError Definition
env@(Env _ e _) ! ident@(i,_,_) =
    case M.lookup i e of
      Just (Alias x) -> env ! x
      Just d -> return d
      Nothing -> throw $ Abstract ident

infix 9 !

-- Check if i == i', modulo Aliases
areEqual :: Env -> Ident -> Ident -> Bool
areEqual env@(Env _ e _) ident@(i,_,_) ident'@(i',_,_) =
    i == i' ||
    case (M.lookup i e , M.lookup i' e) of
      (Just (Alias a), Nothing) -> areEqual env a ident'
      (Nothing, Just (Alias a')) -> areEqual env ident a'
      (Just (Alias a), Just (Alias a')) -> areEqual env a a'
      (_ , _) -> False

-- | Normalization

normalize :: Env -> NF -> TypeError Con
normalize = undefined

normalizeSort :: Env -> NF -> TypeError Sort
normalizeSort env i = do
  con <- normalize env i
  case con of
    NF.Star s -> return s
    _ -> throw $ Normalize i "Expected Sort."

normalizePi :: Env -> NF -> TypeError (Ident, Con, NF)
normalizePi env i = do
  con <- normalize env i
  case con of
    NF.Pi x tyA tyB -> return (x,tyA,tyB)
    _ -> throw $ Normalize i "Expected Pi."

normalizeSigma :: Env -> NF -> TypeError (Ident, Con, NF)
normalizeSigma env i = do
  con <- normalize env i
  case con of
    NF.Sigma x tyA tyB -> return (x,tyA,tyB)
    _ -> throw $ Normalize i "Expected Sigma."

normalizeFin :: Env -> NF -> TypeError [String]
normalizeFin env i = do
  con <- normalize env i
  case con of
    NF.Fin l -> return l
    _ -> throw $ Normalize i "Expected Fin."

normalizeLam :: Env -> NF -> TypeError (Ident, NF)
normalizeLam env i = do
  con <- normalize env i
  case con of
    NF.Lam x t -> return (x,t)
    _ -> throw $ Normalize i "Expected Lambda."

-- Verify that the definition of a variable has well formed tag intro and elim.
checkTag :: Env -> Ident -> Bool
checkTag e@(Env _ ei ee) (i,_,_)  =
    let intro = M.lookup i ei in
    case intro of
      Just (Alias i') -> checkTag e i'
      Just (ITag s) ->
          let elim = fromMaybe [] $ M.lookup i ee
              x = find f elim
              f (ETag _) = True
              f _ = False
          in case x of
               Just (ETag s') | s /= s' -> False
               _ -> True
      _ -> True

elimTag :: Env -> Ident -> String -> Env
elimTag env i s =
  addIntro env i (ETag s)
