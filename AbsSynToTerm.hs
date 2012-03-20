{-# LANGUAGE PackageImports #-}

module AbsSynToTerm where

import Terms 
import qualified RawSyntax as A
import RawSyntax (Identifier(..))
import Control.Monad.Trans.State (runStateT, StateT)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error
import Control.Monad.State
import Control.Applicative
import Data.Functor.Identity
import Data.List
import Basics

type LocalEnv = [String]
type GlobalEnv = ()

type Resolver a = ReaderT LocalEnv (StateT GlobalEnv (ErrorT String Identity)) a


runResolver :: Resolver a -> a
runResolver x = case runIdentity $ runErrorT $ runStateT (runReaderT x []) () of
                  Left err -> error err
                  Right a -> fst a

look :: Identifier -> Resolver Term
look (ident@(Identifier (position,x))) = do
  e <- ask
  case elemIndex x e of
    Nothing -> throwError ("unknown identifier: " ++ show ident)
    Just x -> return $ Bound (Irr position) x

insertVar :: Identifier -> LocalEnv -> LocalEnv
insertVar (Identifier (_pos,x)) e = x:e

dummyVar :: Identifier
dummyVar = Identifier ((0,0),"_")


manyDep binder a []     b = resolveTerm b
manyDep binder a (x:xs) b = binder (Irr x) <$> resolveTerm a <*> local (insertVar x) (manyDep binder a xs b)

manyLam :: [A.Bind] -> A.Exp -> Resolver Term
manyLam []            b = resolveTerm b
manyLam (A.NoBind (A.AIdent x):xs) b = Lam (Irr x) (Hole dummyPosition "") <$> local (insertVar x) (manyLam xs b)
manyLam (A.Bind (A.AIdent x) t:xs) b = Lam (Irr x) <$> resolveTerm t <*> local (insertVar x) (manyLam xs b)

extractVars :: A.Exp -> Resolver [Identifier]
extractVars (A.EVar (A.AIdent i)) = return [i]
extractVars (A.EApp (A.EVar (A.AIdent i)) rest) = (i:) <$> extractVars rest
extractVars _ = throwError "list of variables expected"

resolveTerm :: A.Exp -> Resolver Term
resolveTerm (A.EHole (A.Hole (p,x))) = return $ Hole (Irr p) x
resolveTerm (A.EVar (A.AIdent x)) = look x
resolveTerm (A.ESet (A.Sort (p,"#"))) = return $ Star (Irr p) $ Sort (-1)
resolveTerm (A.ESet (A.Sort (p,'*':s))) = return $ Star (Irr p) $ Sort (read ('0':s))
resolveTerm (A.EProj x (A.AIdent (Identifier (_,field)))) = Proj <$> resolveTerm x <*> pure field
resolveTerm (A.EExtr x (A.AIdent (Identifier (_,field)))) = Extr <$> resolveTerm x <*> pure field
resolveTerm (A.EApp f x) = (:$:) <$> resolveTerm f <*> resolveTerm x
resolveTerm (A.ESigma a b) = case a of
   (A.EAnn vars a') -> do vs <- extractVars vars
                          manyDep Sigma a' vs b
                          
   (A.EAbs _ _ _) -> throwError "cannot use lambda for type"
   _              -> Sigma (Irr dummyVar) <$> resolveTerm a <*> local (insertVar dummyVar) (resolveTerm b)            
resolveTerm (A.EPi a arrow b) = case a of
   (A.EAnn vars a') -> do vs <- extractVars vars
                          manyDep (Pi) a' vs b
                          
   (A.EAbs _ _ _) -> throwError "cannot use lambda for type"
   _              -> Pi (Irr dummyVar) <$> resolveTerm a <*> local (insertVar dummyVar) (resolveTerm b)

resolveTerm (A.EAbs ids _arrow_ b) = manyLam ids b
resolveTerm (A.EPair (A.Decl (A.AIdent i) e) rest) = Pair (Irr i) <$> resolveTerm e <*> local (insertVar i) (resolveTerm rest)
resolveTerm (A.EAnn e1 e2) = Ann <$> resolveTerm e1 <*> resolveTerm e2

