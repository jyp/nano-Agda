{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module TestSyntax where

import Language.LBNF

dumpCode [lbnf|


ESigma.  Exp  ::= "×" ;



|]


test = tokens "×"
