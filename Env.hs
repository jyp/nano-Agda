module Env where

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
    deriving (Show)

type Context = M.Map Ident T.Term
type EnvIntro = M.Map Ident Definition
type EnvElim = M.Map Ident [Definition]

data Env = Env Context EnvIntro EnvElim

type Type = T.Term

getSort :: Env -> Ident -> T.Sort
getSort (Env c _ _) i =
    case fst (c M.! i) of
      T.Star n -> n

addContext :: Env -> Ident -> Type -> Env
addContext (Env c ei ee) i ty =
    Env (M.insert i ty c) ei ee

typePi :: Env -> Ident -> Type -> Ident -> Ident -> T.Term -> Env
typePi (Env context envi enve) i ty x tyA tyB =
    let context' = M.insert i ty context
        envi' = M.insert i (Pi x tyA tyB) envi
    in Env context' envi' enve

typeSigma :: Env -> Ident -> Type -> Ident -> Ident -> T.Term -> Env
typeSigma (Env context envi enve) i ty x tyA tyB =
    let context' = M.insert i ty context
        envi' =  M.insert i (Sigma x tyA tyB) envi
    in Env context' envi' enve

typeFin :: Env -> Ident -> Type -> [String] -> Env
typeFin (Env context envi enve) i ty l =
    let context' = M.insert i ty context
        envi' = M.insert i (Fin l) envi
    in Env context' envi' enve
