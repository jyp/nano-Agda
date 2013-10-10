module Main where

import qualified RawSyntax as R
import qualified Lexer as L
import qualified Parser as P
import Common
import Names
import Terms
import Typing
import Env
import System.Environment(getArgs)

parseFile :: String -> Err [(Ident,Term,Term)]
parseFile f = do
  rawfile <- P.main (L.alexScanTokens f)
  R.convertFile rawfile

parseFiles :: [String] -> Err [(Ident,Term,Term)]
parseFiles l = do
  l' <- mapM parseFile l
  return (concat l')

checkFiles :: [(Ident,Term,Type)] -> Err [(Env,Term)]
checkFiles decs = do
  decsT <- mapM (convert . checkDec) decs
  return decsT

main = do
  args <- getArgs
  files <- mapM readFile args
  let decs = parseFiles files
  let results = decs >>= checkFiles
  return ()
