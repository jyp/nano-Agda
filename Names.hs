module Names where

import Control.Monad.State

import Data.Map as M

type Name = Int

incr :: Name -> Name
incr n = n + 1

-- | Position stuff

type Position = (Int,Int)

dummyPos :: Position
dummyPos = (-1, -1)

-- | Identifier aka, Names with source informations

type Ident = (Name,String,Position)

-- | Name Environment

type NameEnv = Map String Ident

type EnvM = State (NameEnv, Name)

getIdent :: String -> EnvM Ident
getIdent s = do
  (m,_) <- get
  return (m M.! s)

freshIdent :: (String, Position) -> EnvM Ident
freshIdent (s,p) = do
  (m,c) <- get
  let ident = (c,s,p)
  let m' = M.insert s ident m
  _ <- put (m' , incr c)
  return ident

freshIdentNoPos :: String -> EnvM Ident
freshIdentNoPos s = freshIdent (s,dummyPos)

runEnvFrom :: (NameEnv, Name) -> EnvM a -> a
runEnvFrom s x = evalState x s

runEnv :: EnvM a -> a
runEnv = runEnvFrom (M.empty, 0)
