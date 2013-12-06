module Names where

import qualified PPrint as P
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

-- | Pretty positions
instance P.Pretty Position where
    pretty (Point l c) = l P.<:> c
    pretty (Range l1 c1 l2 c2) | l1 == l2 =
         l1 P.<:> c1 P.<.> c2
    pretty (Range l1 c1 l2 c2) =
         l1 P.<.> l2 P.<:> c1 P.<.>  c2

dummyPos :: Position
dummyPos = Point (-1) (-1)

-- | Identifier aka, Names with source informations

newtype Ident = I (Name,String,Position)

-- | Pretty identifier
instance P.Pretty Ident where
    pretty (I (i,n,_)) = P.text n P.<> P.subscriptPretty i

instance Eq Ident where
    I (x,_,_) == I (y,_,_) = x == y

(>~) :: Ident -> (Name -> Name) -> Ident
I (x,s,p) >~ f = I (f x, s, p)

infix 1 >~

swapWith :: Ident -> Ident -> Ident -> Ident
swapWith n n' k =
    if k == n then n' else k

getPos :: Ident -> Position
getPos (I (_,_,p)) = p

getN :: Ident -> Name
getN (I (n,_,_)) = n

-- | Name Environment

type NameEnv = Map String Ident

getIdent :: NameEnv -> (String,Position) -> Maybe Ident
getIdent e (s,p) =
    fmap (\(I (c,s',_)) -> I (c,s',p)) $ M.lookup s e

freshIdent :: NameEnv -> (String, Position) -> FreshM (NameEnv,Ident)
freshIdent e (s,p) = do
  name <- fresh
  let ident = I (name , s , p)
  let m' = M.insert s ident e
  return (m',ident)

freshIdentNoPos :: NameEnv -> String -> FreshM (NameEnv,Ident)
freshIdentNoPos e s = freshIdent e (s,dummyPos)

-- | Sort

type Sort = Int

-- | Pretty declaration

instance (P.Pretty a, P.Pretty b) => P.Pretty (Ident,a,b) where
    pretty (i,t,ty) =
        (P.pretty i P.<+> P.dcolons) P.$+> P.pretty ty P.$+$
        (P.pretty i P.<+> P.equals) P.$+> P.pretty t
