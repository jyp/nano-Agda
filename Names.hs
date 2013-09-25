module Names where

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Arrow ((&&&))

type Name = Int

type FreshM = State Int

-- | New fresh Id
fresh :: FreshM Name
fresh = state (id &&& succ)

infixl 4 <.>
-- | Applies a pure value in an applicative computation
(<.>) :: Applicative f => f (a -> b) -> a -> f b
m <.> x = m <*> pure x

runFreshM :: FreshM a -> a
runFreshM m = evalState m 0

runFreshMFrom :: Name -> FreshM a -> a
runFreshMFrom n m = evalState m n
