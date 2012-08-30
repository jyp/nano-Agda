{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving #-}
module Basics
       (module Monoid,
        module Control.Applicative,
        Irr(..), 
        Sort(..),
        above, oneLev, zero,
        Ident, Identifier(..), DisplayContext,
        Position, dummyPosition, identPosition, 
        isDummyId, modId, synthId, dummyId, idString,
        Lattice(..)) where

import Display
import qualified RawSyntax as A
import RawSyntax (Identifier(..))
import Control.Applicative
import Monoid
import Data.Sequence (Seq)


-----------
-- Irr

newtype Irr a = Irr {fromIrr :: a}
    deriving Show

instance Eq (Irr a) where
    x == y = True

instance Pretty x => Pretty (Irr x) where
    pretty (Irr x) = pretty x

--------------
-- Ident
instance Pretty Identifier where
    pretty (Identifier (_,x)) = text x


type Ident = Irr Identifier

isDummyIdS ('_':x) = True
isDummyIdS _ = False

isDummyId (Irr (Identifier (_,xs))) = isDummyIdS xs

synthId :: String -> Ident
synthId x = Irr (Identifier (fromIrr $ dummyPosition,x))

dummyId = synthId "_"

idString :: Ident -> String
idString (Irr (Identifier (_,name))) = name

type DisplayContext = Seq Ident

----------------
-- Position

type Position = (Int,Int)

identPosition (Irr (Identifier (p,_))) = Irr p

dummyPosition = Irr (0,0)

modId :: (String -> String) -> Ident -> Ident
modId f (Irr (Identifier (pos ,x)))  = (Irr (Identifier (pos,f x)))

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



