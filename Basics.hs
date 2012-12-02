{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving #-}
module Basics
       (module Data.Monoid,
        module Control.Applicative,
        Sort(..),
        above, oneLev, zero,
        Ident(..), DisplayContext,
        Position, dummyPosition, 
        isDummyId, modId, synthId, dummyId, 
        Lattice(..)) where

import Display
import Control.Applicative
import Data.Sequence (Seq)
import Data.Monoid

--------------
-- Ident
instance Pretty Ident where
    pretty (Ident _ x) = text x


data Ident = Ident {identPosition :: Position, idString :: String}
  deriving (Show,Eq)

isDummyIdS ('_':x) = True
isDummyIdS _ = False

isDummyId (Ident _ xs) = isDummyIdS xs

synthId :: String -> Ident
synthId = Ident dummyPosition 

dummyId = synthId "_"

type DisplayContext = Seq Ident

----------------
-- Position

type Position = (Int,Int)

dummyPosition = (0,0)

modId :: (String -> String) -> Ident -> Ident
modId f (Ident pos x)  = Ident pos (f x)

------------------
-- Sort

instance Lattice Int where
    (⊔) = max

class Lattice a where
    (⊔) :: a -> a -> a

instance Ord Sort where
  compare (Sort x) (Sort y) = compare x y

newtype Sort = Sort {sortLevel :: Int}
  deriving (Eq,Num)

instance Lattice Sort where
  x ⊔ Sort (-1) = Sort (-1) -- is this a lattice? 
  Sort x ⊔ Sort y = Sort (x ⊔ y)

instance Show Sort where
    show s = render (pretty s)


instance Pretty Sort where
    pretty s = prettyLev s
    
star = "∗" -- ⋆★*∗

prettyLev (Sort (-1) ) = "□"
prettyLev (Sort 0    ) = star <> mempty
prettyLev (Sort l    ) = star <> subscriptPretty l

above (Sort l) = Sort (l + 1)
oneLev = Sort 1

zero = Sort 0



