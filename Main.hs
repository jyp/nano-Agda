module Main where

import qualified RawSyntax as R
import qualified Lexer
import qualified Parser
import PPrint(pretty)
import Common
import Names
import Terms
import Typing
import Env
import System.Environment(getArgs)
import Control.Monad.Error

parseFiles :: [String] -> Err [R.Smt]
parseFiles l = do
  l' <- mapM (Parser.main . Lexer.alexScanTokens) l
  return (concat l')

checkFiles :: [(Ident,Term,Term)] -> Err (Env, [(Ident, Ident, Ident)])
checkFiles decs = do
  decsT <- scanfoldl
          (\e s -> convert $ checkDec e s) empty decs
  return decsT

printExn :: Show a => ErrorT e IO a -> IO ()
printExn e = do
    e' <- runErrorT e
    case e' of
      Left _ -> return ()
      Right x -> print x

main :: IO ()
main = do
  args <- getArgs
  files <- mapM readFile args
  -- () <- print files

  let decsAST = parseFiles files
  -- () <- printExn decsAST

  let decsTerms = decsAST >>= R.convertFile
  () <- printExn (fmap pretty decsTerms)

  results <- runErrorT $ decsTerms >>= checkFiles
  case results of
    Left x -> print (pretty x)
    Right x -> print (pretty x)
