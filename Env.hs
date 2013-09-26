module Env where

import Names
import Terms

import qualified Data.Map as M

data Definition
    = Appl Ident Ident -- y = f x
    | Fun Ident Term   -- f = λx.t
    | Tag String       -- x = 'tag
    | Pair Ident Ident -- z = (x,y)
    deriving (Show)

type Context = M.Map Ident Term
type Env = M.Map Ident Definition
