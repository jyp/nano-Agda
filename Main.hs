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
import Control.Monad.Writer(WriterT,runWriterT)

parseFiles :: [String] -> Err [R.Smt]
parseFiles l = do
  l' <- mapM (Parser.main . Lexer.alexScanTokens) l
  return (concat l')

checkFiles :: [(Ident,Term,Term)] -> Err Env
checkFiles decs = do
  decsT <- convert $ checkDecs empty decs
  return decsT

printExn :: Show a => Err a -> IO ()
printExn e = do
    (e',_trace) <- runWriterT $ runErrorT e
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
  () <- printExn $ fmap pretty decsTerms

  returnErr 3 $ decsTerms >>= checkFiles
