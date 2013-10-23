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

(=~) :: Ident -> Ident -> Bool
(x,_,_) =~ (y,_,_) = x == y

infix 7 =~

(>~) :: Ident -> (Name -> Name) -> Ident
(x,s,p) >~ f = (f x, s, p)

infix 1 >~

getPos :: Ident -> Position
getPos (_,_,p) = p

getN :: Ident -> Name
getN (n,_,_) = n

-- | Name Environment

type NameEnv = Map String Ident

getIdent :: NameEnv -> (String,Position) -> Maybe Ident
getIdent e (s,p) =
    fmap (\(c,s',_) -> (c,s',p)) $ M.lookup s e

freshIdent :: NameEnv -> (String, Position) -> FreshM (NameEnv,Ident)
freshIdent e (s,p) = do
  name <- fresh
  let ident = (name , s , p)
  let m' = M.insert s ident e
  return (m',ident)

freshIdentNoPos :: NameEnv -> String -> FreshM (NameEnv,Ident)
freshIdentNoPos e s = freshIdent e (s,dummyPos)
