{-# LANGUAGE TupleSections #-}

module AbsSynToTerm where

import Normal
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
    Just x -> return $ V position x

insertVar :: Identifier -> LocalEnv -> LocalEnv
insertVar (Identifier (_pos,x)) e = x:e

insertVars :: [Identifier]-> LocalEnv -> LocalEnv
insertVars [] = id
insertVars (x:xs) = insertVars xs . insertVar x

dummyVar :: Identifier
dummyVar = Identifier ((0,0),"_")

i2i (Identifier (p,s)) = Ident p s

manyDep binder a []     b = resolveTerm b
manyDep binder a (x:xs) b = binder (i2i x) <$> resolveTerm a <*> local (insertVar x) (manyDep binder a xs b)

manyLam :: [A.Bind] -> A.Exp -> Resolver Term
manyLam []            b = resolveTerm b
manyLam (A.NoBind (A.AIdent x):xs) b = Lam (i2i x) (Hole dummyPosition "") <$> local (insertVar x) (manyLam xs b)
manyLam (A.Bind (A.AIdent x) t:xs) b = Lam (i2i x) <$> resolveTerm t <*> local (insertVar x) (manyLam xs b)

extractVars :: A.Exp -> Resolver [Identifier]
extractVars (A.EVar (A.AIdent i)) = return [i]
extractVars (A.EApp (A.EVar (A.AIdent i)) rest) = (i:) <$> extractVars rest
extractVars _ = throwError "list of variables expected"

resolveTerm :: A.Exp -> Resolver Term
resolveTerm (A.EHole (A.Hole (p,x))) = return $ Hole p x
resolveTerm (A.EVar (A.AIdent x)) = look x
resolveTerm (A.ESet (A.Sort (p,"#"))) = return $ Star p $ Sort (-1)
resolveTerm (A.ESet (A.Sort (p,'*':s))) = return $ Star p $ Sort (read ('0':s))
resolveTerm (A.ESplit x idents c) = Split <$> resolveTerm x 
                                          <*> pure [f | (A.AIdent (Identifier (_,f))) <- idents]
                                          <*> local (insertVars [f | A.AIdent f <- idents]) (resolveTerm c)
resolveTerm (A.EApp f x) = App <$> resolveTerm f <*> resolveTerm x <*> pure (var 0)
resolveTerm (A.ESigma decls) = sigma <$> (resolveDecls =<< mapM decodeDecl decls)
resolveTerm (A.EPi a arrow b) = do
  (vs,a') <- decodeDecl a
  manyDep Pi a' vs b

resolveTerm (A.EAbs ids _arrow_ b) = manyLam ids b
resolveTerm (A.EPair defs) = pair <$> (forM defs $ \(A.Def (A.AIdent i@(Identifier (_p,f))) e) -> do
                                          e' <- resolveTerm e
                                          return (f,e'))
resolveTerm (A.EAnn e1 e2) = Ann <$> resolveTerm e1 <*> resolveTerm e2
resolveTerm (A.EBox (A.AIdent i) t e) = Box (i2i i) <$> resolveTerm t <*> local (insertVar i) (resolveTerm e) <*> pure (map var [0..])

resolveTerm (A.EFin ts) = return $ Fin [t | (A.AIdent i@(Identifier (_p,t))) <- ts]
resolveTerm (A.ETag (A.AIdent i@(Identifier (_p,t)))) = return $ Tag t
resolveTerm (A.ECas x cs) = Cas <$> resolveTerm x <*> (forM cs $ \(A.Def (A.AIdent i@(Identifier (_p,t))) e) -> do
                                                          e' <- resolveTerm e
                                                          return (t,e'))

decodeDecl d = case d of
   (A.EAnn vars a') -> do vs <- extractVars vars
                          return (vs,a')
                          
   (A.EAbs _ _ _) -> throwError "cannot use lambda for type"
   _              -> return ([dummyVar],d)

resolveDecls :: [([Identifier],A.Exp)]-> Resolver [(String,Term)]
resolveDecls [] = return []
resolveDecls (([],_):ds) = resolveDecls ds
resolveDecls ((v@(Identifier (_p,f)):vs,t):ds) = (:) <$> ((f,) <$> resolveTerm t) <*> local (insertVar v) (resolveDecls ((vs,t):ds))
