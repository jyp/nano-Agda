{-# LANGUAGE DeriveDataTypeable #-}

module Options (Args(..),TypeSystem(..),options) where

import System.Console.CmdArgs.Implicit
import System.IO.Unsafe

data TypeSystem = CCω
                | Predicative
  deriving (Show, Data, Typeable)

data Args = 
  Args {verb :: Int,
        typeSystem :: TypeSystem,
        showRelevance :: Bool,
        collapseRelevance :: Bool,
        ignoreBinder :: Bool,
        files :: [String]
        } 
  deriving (Show, Data, Typeable)
           
sample = cmdArgsMode $ 
         Args { verb = 0 &= help "verbosity" &= opt (0 :: Int),
                typeSystem = enum [CCω &= name "I" &= help "CCω (Impredicative)",
                                   Predicative &= name "P" &= help "Martin-Löf (Predicative)"
                                   ]
                               , -- &= opt (0 :: Int),
                showRelevance = False &= help "display more irrelevance annotations in normal forms",
                collapseRelevance  = False &= help "! (param) does not generate new relevance levels.",
                ignoreBinder  = False &= help "ignore binder annotations.",
                files = [] &= args &= typFile
              }
         
         
options = unsafePerformIO (cmdArgsRun sample)
