module Names where

import Control.Monad.State
import Control.Arrow ((&&&))

import Data.Map as M

type Name = Int

incr :: Name -> Name
incr n = n + 1

type FreshM = State Name

fresh :: FreshM Name
fresh = state ( id &&& succ )

runFreshFrom :: Name -> FreshM a -> a
runFreshFrom s x = evalState x s

runFresh :: FreshM a -> a
runFresh = runFreshFrom 0

-- | Position stuff

data Position
    = Range Int Int Int Int
    | Point Int Int
      deriving (Ord,Eq)

dummyPos :: Position
dummyPos = Point (-1) (-1)

-- | Identifier aka, Names with source informations

type Ident = (Name,String,Position)

-- | Name Environment

type NameEnv = Map String Ident

getIdent :: NameEnv -> (String,Position) -> Ident
getIdent e (s,p) = do
  let (c,s',_) = e M.! s in (c,s',p)

freshIdent :: NameEnv -> (String, Position) -> FreshM (NameEnv,Ident)
freshIdent e (s,p) = do
  name <- fresh
  let ident = (name , s , p)
  let m' = M.insert s ident e
  return (m',ident)

freshIdentNoPos :: NameEnv -> String -> FreshM (NameEnv,Ident)
freshIdentNoPos e s = freshIdent e (s,dummyPos)
