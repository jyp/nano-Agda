module Env where

import Common

import Names
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
    deriving (Show, Eq)

type Context = M.Map Ident T.Term
type EnvIntro = M.Map Ident Definition
type EnvElim = M.Map Ident [Definition]

data Env = Env Context EnvIntro EnvElim

getSort :: Env -> Ident -> T.Sort
getSort (Env c _ _) i =
    case fst (c M.! i) of
      T.Star n -> n

getType :: Env -> Ident -> T.Type
getType (Env c _ _) i = c M.! i

getIntro :: Env -> Ident -> Definition
getIntro (Env _ e _) i = e M.! i

getElims :: Env -> Ident -> [Definition]
getElims (Env _ _ e) i = e M.! i

getVal :: Env -> Ident -> Either Definition [Definition]
getVal e@(Env _ ei ee) i =
    case M.lookup i ei of
      Just (Alias x) -> getVal e x
      Just x -> Left x
      Nothing -> Right $ ee M.! i

addContext :: Env -> Ident -> T.Type -> TypeError Env
addContext (Env context ei ee) i ty = do
    context' <-
        case M.lookup i context of
          Nothing -> return (M.insert i ty context)
          Just ty' | ty == ty' -> return (M.insert i ty context)
          Just ty' -> throw (IncompBindings i ty ty')
    return (Env context' ei ee)

addBinding :: Env -> Ident -> Definition -> T.Type -> TypeError Env
addBinding env i t ty = do
  (Env context ei ee) <- addContext env i ty
  let ei' = M.insert i t ei
  return (Env context ei' ee)

addAlias :: Env -> Ident -> Ident -> TypeError Env
addAlias env x y =
    addBinding env x (Alias y) (getType env y)

-- Intro Type in the environment

typePi :: Env -> Ident -> T.Type -> Ident -> Ident -> T.Term -> TypeError Env
typePi env i ty x tyA tyB = do
  Env context envi enve <- addContext env i ty
  envi' <- return (M.insert i (Pi x tyA tyB) envi)
  return (Env context envi' enve)

typeSigma :: Env -> Ident -> T.Type -> Ident -> Ident -> T.Term -> TypeError Env
typeSigma env i ty x tyA tyB = do
  Env context envi enve <- addContext env i ty
  envi' <- return (M.insert i (Sigma x tyA tyB) envi)
  return (Env context envi' enve)

typeFin :: Env -> Ident -> T.Type -> [String] -> TypeError Env
typeFin env i ty l = do
  Env context envi enve <- addContext env i ty
  envi' <- return (M.insert i (Fin l) envi)
  return (Env context envi' enve)

elimPair :: Env -> Ident -> Ident -> Ident -> TypeError Env
elimPair env@(Env c ei ee) x' y' z =
    case M.lookup z ei of
      Just (IPair x y) ->
          do { env' <- addAlias env x' x ; addAlias env' y' y }
      Nothing ->
          return $ Env c (M.insert z (EPair x' y') ei) ee
