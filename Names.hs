module Names where

import Control.Monad.State

import Data.Map as M

type Name = Int

incr :: Name -> Name
incr n = n + 1

-- | Position stuff

data Position
    = Range Int Int Int Int
    | Point Int Int
      deriving (Ord,Eq)

dummyPos :: Position
dummyPos = Point (-1) (-1)

instance Show Position where
    show (Point l c) = show l ++ ":" ++ show c
    show (Range l1 c1 l2 c2) | l1 == l2 =
        show l1 ++ ":" ++  show c1 ++ "." ++ show c2
    show (Range l1 c1 l2 c2) =
        show l1 ++ "." ++ show l2 ++ ":" ++
        show c1 ++ "." ++ show c2

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
