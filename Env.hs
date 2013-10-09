module Env where

import Common

import Names
import qualified Terms as T

import qualified Data.Map as M

data Definition
    = Appl Ident Ident          -- y = f x
    | Fun Ident T.Term          -- f = λx.t
    | Tag String                -- x = 'tag
    | Pair Ident Ident          -- z = (x,y)
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

addContext :: Env -> Ident -> T.Type -> TypeError Env
addContext (Env context ei ee) i ty = do
    context' <-
        case M.lookup i context of
          Nothing -> return (M.insert i ty context)
          Just ty' | ty == ty' -> return (M.insert i ty context)
          Just ty' -> throw (IncompBindings i ty ty')
    return (Env context' ei ee)

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

