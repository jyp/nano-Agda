{- LANGUAGE CPP #-}
module Monoid (module Monoid, module Data.Monoid) where

-- This module's only purpose is to maintain compatiblility.

#if __GLASGOW_HASKELL__ < 703
import Data.Monoid
#else
-- We do not reuse `(<>)' from `Data.Monoid' since it is associative to the
-- right.
import Data.Monoid hiding ((<>))
#endif

(<>) :: Monoid a => a -> a -> a
(<>) = mappend

