module Main where

import Data.Either
import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs )
import Options 
import Terms

import RawSyntax
import AbsSynToTerm
import TypeChecker
import Basics
import Display
import Text.PrettyPrint.HughesPJ (render)
import qualified Data.Sequence as S
import System.FilePath
import System.Directory
import Control.Monad.Error

import Language.LBNF.Runtime (ParseMonad(..))

instance Error Doc where
  noMsg = "nanoAgda: unknown error"
  strMsg = text

myLLexer = tokens 

type Verbosity = Int

putStrV :: Verbosity -> Doc -> Checker ()
putStrV v s = if verb options >= v then liftIO $ putStrLn (render s) else return ()

-- | The file containing the type of the term contained in file @f@
typeFile f = replaceExtension f "type.na"

runFile :: FilePath -> Checker Value
runFile f = do
  putStrV 1 $ "Processing file:" <+> text f
  contents <- liftIO $ readFile f
  run contents f

instance Pretty Token where
    pretty = text . show

type Checker a = (ErrorT Doc IO) a

run :: String -> FilePath -> Checker Value
run s fname = let ts = myLLexer s in case pExp ts of
   Bad err -> do 
     putStrV 1 $ "Tokens:" <+> pretty ts
     throwError $ text $ fname ++ ": parse failed: " ++ err
   Ok tree -> do
     process fname tree

getType :: FilePath -> Checker Value
getType fname = do
  let t = typeFile fname
  putStrV 10 $ "typeFile = " <> text t
  ex <- liftIO $ doesFileExist t
  if ex  
    then do putStrV 2 $ "Using type from file: " <> text t
            runFile t 
    else do putStrV 2 "Using default type" 
            return (Star dummyPosition 1)

process :: FilePath -> Exp -> Checker Value
process fname modul = do
  typ <- getType fname
  let resolved = runResolver $ resolveTerm modul
  putStrV 4 $ "[Resolved into]" $$ pretty resolved
  let (checked,info) = runChecker (resolved,typ) $ cType mempty resolved typ
  mapM (putStrV 0) info  -- display constraints, etc.
  case checked of
    Right a -> do 
       putStrV 0 $ "nf =" <+> pretty a
       return a
    Left (e,err) -> do let (line,col) = termPosition e 
                       throwError $ (text fname <> ":" <> pretty line <> ":" <> pretty (col - 1) <> ": " <> err)
                       
      
main :: IO ()
main = do 
  results <- forM (files options) $ \f -> runErrorT $ runFile f
  let (errs,oks) = partitionEithers results
  mapM (putStrLn . render) errs               
  putStrLn $ show (length oks) ++ "/" ++ show (length results) ++ " files typecheck."

