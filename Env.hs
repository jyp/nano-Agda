module Env where

import Common

import Names
import PPrint
import Text.PrettyPrint(($$),($+$),(<>),(<+>),text)
import qualified Text.PrettyPrint as P
import qualified Terms as T

import qualified Data.Map as M

data Definition
    = Appl Ident Ident          -- y = f x
    | Fun Ident T.Term          -- f = λx.t
    | ITag String               -- x = 'tag
    | ETag String               -- x = 'tag
    | IPair Ident Ident         -- z = (x,y)
    | EPair Ident Ident         -- (x,y) = z
    | Alias Ident               -- z = z'
    | Pi Ident Ident T.Term     -- σ = (x:A)→B
    | Sigma Ident Ident T.Term  -- σ = (x:A)×B
    | Fin [String]              -- σ = { 'bla, 'bli, 'blo }
    | Star Int                  -- σ = *ᵢ
    deriving (Eq)

instance Pretty Definition where
    pretty (Appl f x) = pretty f <+> pretty x
    pretty (Fun i t) = lamP i t
    pretty (ITag x) = text x <> intro
    pretty (ETag x) = text x <> elim
    pretty (IPair x y) = pairP x y <> intro
    pretty (EPair x y) = pairP x y <> elim
    pretty (Alias x) = pretty x
    pretty (Pi x tyA tyB) = piP x tyA tyB
    pretty (Sigma x tyA tyB) = sigmaP x tyA tyB
    pretty (Fin l) = finP l
    pretty (Star i) = sort i

type Context = M.Map Name T.Type
type EnvIntro = M.Map Name Definition
type EnvElim = M.Map Name [Definition]

data Env = Env Context EnvIntro EnvElim
    deriving (Eq)

instance Pretty Env where
    pretty (Env c ei _) =
        P.text "Context :" <+> pretty c $+$
        P.text "EnvIntro :" <+> pretty ei

instance Pretty (Env, [(Ident, Ident, Ident)]) where
    pretty (e,l) =
        pretty e $+$ (P.vcat $ map printdef l)
            where
              printdef (i,t,ty) =
                  pretty i
                  <+> P.colon <+> pretty ty
                  <+> P.equals <+> pretty t

empty :: Env
empty = Env M.empty M.empty M.empty

getType :: Env -> Ident -> TypeError T.Type
getType (Env c _ _) ident@(i,_,_) =
    case M.lookup i c of
      Just t -> return t
      Nothing ->
          throw . UnknownError $
          text "Variable" <+> pretty ident <+>
          text "doesn't have a type."

getIntro :: Env -> Ident -> TypeError Definition
getIntro (Env _ e _) ident@(i,_,_) =
    case M.lookup i e of
      Just t -> return t
      Nothing ->
          throw . UnknownError $
          text "Variable" <+> pretty ident <+>
          text "doesn't have an introduction."

getElims :: Env -> Ident -> TypeError [Definition]
getElims (Env _ _ e) ident@(i,_,_) =
    case M.lookup i e of
      Just t -> return t
      Nothing ->
          throw . UnknownError $
          text "Variable" <+> pretty ident <+>
          text "doesn't have any elimination."

getVal :: Env -> Ident -> Either Definition [Definition]
getVal e@(Env _ ei ee) (i,_,_) =
    case M.lookup i ei of
      Just (Alias x) -> getVal e x
      Just x -> Left x
      Nothing -> Right $ ee M.! i

addContext :: Env -> Ident -> T.Type -> TypeError Env
addContext (Env context ei ee) id@(i,_,_)  ty = do
    context' <-
        case M.lookup i context of
          Nothing -> return (M.insert i ty context)
          Just ty' | ty == ty' -> return (M.insert i ty context)
          Just ty' -> throw (IncompBindings id ty ty')
    return (Env context' ei ee)

addBinding :: Env -> Ident -> Definition -> T.Type -> TypeError Env
addBinding env id@(i,_,_) t ty = do
  (Env context ei ee) <- addContext env id ty
  let ei' = M.insert i t ei
  return (Env context ei' ee)

addAlias :: Env -> Ident -> Ident -> TypeError Env
addAlias env x y = do
  ty <- getType env y
  addBinding env x (Alias y) ty

-- | Verification functions


-- Utility function to normalize (and verify) a sort.
normalizeSort :: Env -> Ident -> TypeError T.Sort
normalizeSort env@(Env _ e _) id@(i,_,_) =
    case M.lookup i e of
      Just (Star s) -> return s
      Just (Alias x) -> normalizeSort env x
      _ -> throw $ Abstract id

normalizeSort' :: Env -> T.Type -> TypeError T.Sort
normalizeSort' e ty =
    case ty of
      T.Sort s -> return s
      T.Below i -> fmap (\s -> s-1) (normalizeSort' e i)
      T.Ident i -> normalizeSort e i

-- Intro Type in the environment

typePi :: Env -> Ident -> T.Type -> Ident -> Ident -> T.Term -> TypeError Env
typePi env i ty x tyA tyB =
  addBinding env i (Pi x tyA tyB) ty

typeSigma :: Env -> Ident -> T.Type -> Ident -> Ident -> T.Term -> TypeError Env
typeSigma env i ty x tyA tyB = do
  addBinding env i (Sigma x tyA tyB) ty

typeFin :: Env -> Ident -> T.Type -> [String] -> TypeError Env
typeFin env i ty l = do
  addBinding env i (Fin l) ty
