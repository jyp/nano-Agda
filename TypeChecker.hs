{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances, GADTs, TupleSections, GeneralizedNewtypeDeriving, OverloadedStrings #-}

module TypeChecker where

import Prelude hiding (length)
import Basics
import Display
import Control.Monad.Error
import Data.Maybe
import Control.Monad.Writer
import Control.Monad.Reader
import Data.Functor.Identity
import Data.Sequence hiding (replicate,zip,reverse)
import Terms

instance Error (Term,Doc) where
  strMsg s = (hole "strMsg: panic!",text s)

newtype Result a = Result (
  (ReaderT (Term,Type)) -- the module being type-checked and its type (in normal form)
  ((ErrorT (Term,Doc)) -- term is used for position information
  (Writer [Doc])) a)
 deriving (Functor, Applicative, Monad, MonadReader (Term,Type), MonadError (Term,Doc), MonadWriter [Doc])

report :: Doc -> Result ()
report x = tell [x]

runChecker :: (Term,Type) -> Result a -> (Either (Term,Doc) a,[Doc])
runChecker x (Result m) = runIdentity $ runWriterT $ runErrorT $ runReaderT m x

type Value    = NF
type Type     = Value
data Bind     = Bind {entryIdent :: Ident, 
                      entryType :: Type   -- ^ Note: the context of the type does not contain the variable bound here.
                     }
type Context  = Seq Bind

display :: Context -> NF -> Doc
display c = prettyTerm (fmap entryIdent c)

dispContext :: Context -> Doc
dispContext ctx = case viewl ctx of
  EmptyL -> mempty
  Bind x typ :< ctx' -> (pretty x <+> ":" <+> display ctx' typ) $$ dispContext ctx'

-- FIXME: flag an error if impredicativity disabled and we use it anyway.

-- | Infer a type and evaluate to normal form
iType :: Context -> Term -> Result (Value,Type)
iType g (Ann e et) = do
  (et',o) <- iSort g et 
  e' <- cType g e et'
  return (e',et') -- type annotations are removed once they're checked
iType g t@(Star p s) =  return (Star p s,Star p $ above s)  
iType g (Pi ident tyt tyt')  = do
    (ty ,s1) <- iSort g tyt 
    (ty',s2) <- iSort (Bind ident ty <| g) tyt'
    let o = s1 ⊔ s2
    return (Pi ident ty ty', Star (identPosition ident) o)
iType g (Sigma i []) = return (Sigma i [],Star i 0)          
iType g (Sigma i ((f,t):ts)) = do
   (t',s1)  <- iSort g t 
   (Sigma _ ts',s2) <- iSort (Bind (synthId f)  t' <| g) (Sigma i ts)
   let o = s1 ⊔ s2          
   return (Sigma i ((f,t'):ts'), Star i o)
iType g e@(V _ x) = do
  return $ (var x, wkn (x+1) ∙ typ)
  where Bind _ typ = g `index` x
        
iType g (Hole p x) = do
  report $ hang (text ("context of " ++ x ++ " is")) 2 (dispContext g)
  return (Hole p x, Hole p ("type of " ++ x))

iType g t@(Lam x (Hole _ _) e) = throwError (t,"cannot infer type for" <+> display g t)
iType g (Lam x ty e) = do
    (vty,vs) <- iSort g ty
    (ve,t) <- iType (Bind x  vty <| g) e
    return $ (Lam x vty ve, Pi x vty t)

iType g (Pair p fs) = do
  (fs,vs,ts) <- unzip3 <$> (forM fs $ \(f,x) -> do 
                            (x',xt) <- iType g x
                            return (f,x',xt))
  return (Pair p (zip fs vs),Sigma p (zip fs [ wkn n ∙ t | (n,t) <- zip [0..] ts])) 
  -- possible dependencies in the type are not discovered 
  
iType g (Fin p ts) = return (Fin p ts,Star p 0)
  
iType g (App e1 e2) = do
   (e1',et) <- iType g e1
   et' <- whnf g et
   case et' of
     Pi _ ty ty' -> do 
          v2 <- cType g e2 ty
          return (app e1' v2, subst0 v2 ∙ ty') 
     _             ->  throwError (e1,"type should be function:" <> display g et)

iType g (Proj e f) = do
  (e',et) <- iType g e
  et' <- whnf g et
  case et' of 
    Sigma _ fs -> case projType e f fs of
                    Just tt -> return (proj e f,tt)
                    _ -> throwError (e,"field" <+> text f <+> "not found in type" <+> display g et')
    _ -> throwError (e,hang "expected record:" 2 $ sep ["term:" <+> display g e,
                                                        "type:" <+> display g et,
                                                        "field:" <+> text f])
    
iType g c@(Cas i q e cs) = do
  let p = identPosition i
      et = Fin p $ map fst cs
  e' <- cType g e et
  (q',_) <- iSort g q 

  cs' <- forM cs $ \ (x,v) -> do
     v' <- cType g v (subst0 (Tag p x) ∙ q')
     return (x,v')
  return (cas i q' e' cs',subst0 e' ∙ q')
      
    
iType g This = do
  (_,thist) <- ask
  return (This, thist)

iType g t = throwError (t,hang "cannot infer type for" 2 $ display g t)
         
-- | Infer a sort, and normalise
iSort :: Context -> Term -> Result (Type,Sort)
iSort g e = do
  (val,v) <- iType g e
  v' <- whnf g v
  case v' of 
    Star _ i -> return (val,i)
    Hole _ h -> do 
         report $ text h <+> "must be a type"
         return $ (hole h, Sort 1)
    _ -> throwError (e,display g e <+> "is not a type")


-- | Check the type and normalize
cType0 :: Context -> Term -> Type -> Result Value
cType0 g (Lam name (Hole _ _) e) (Pi name' ty ty') = do
        e' <- cType (Bind name ty <| g) e ty'
        return (Lam name ty e') -- the type and binder is filled in.

cType0 g (Lam name ty0 e) (Pi name' ty ty')
  =     do (t,_o) <- iSort g ty0
           unify g (Hole (identPosition name) (show name)) ty t
           e' <- cType (Bind name ty <| g) e ty'
           return (Lam name ty e')

-- note: there is automatic coercion of values to more specific types.
cType0 g (Pair p _ignored) (Sigma _ []) = return $ Pair p []
cType0 g (Pair p ((f,x):xs)) (Sigma i fs@((f',xt):xts)) 
  | f /= f' = do  Pair _ fs' <- cType g (Pair p xs) (Sigma p fs)
                  return $ Pair p ((f,x):fs')
  | f == f' = do
    x' <- cType g x xt
    -- report $ hang "Remains to check: " 2 $ sep ["pair:" <+> display g (pair xs), "type:" <+>  display g (subst0 x' ∙ sigma xts)]
    Pair _ xs' <- cType g (Pair p xs) (subst0 x' ∙ Sigma p xts)
    return (Pair p ((f,x'):xs'))

cType0 g e@(Tag p t) ty@(Fin p' ts) 
  | t `elem` ts = return e
  | otherwise = throwError (e,vcat ["tag: " <> text t, "not in: " <> display g ty])

cType0 g e v = do 
  -- report $ hang "no checking rule for" 2 $ vcat ["term = " <> display g e, "type = " <>display g v]
  (e',v') <- iType g e
  unify g e v' v
  return e'
  
-- | Unification
unify :: Context -> Term -> Type -> Type -> Result ()
unify g0 e q0' q0 = unif g0 q0' q0 where 
   unif, unif' :: Context -> Type -> Type -> Result ()
   unif' g q' q = do x' <- whnf g q'
                     x <- whnf g q
                     unif g x' x
   unif g q' q = case (q',q) of
     (Star _ s , Star _ s') -> check $ s == s'
     (Pi i a b , Pi _ a' b') -> (a' <: a) >> unif (Bind i a <| g) b b'
     (Lam i a b , Lam _ a' b') -> (a' <: a) >> unif (Bind i a <| g) b b'
     (App a b , App a' b') -> unif g a a' >> (b <: b')
     (Sigma _ [], Sigma _ []) -> return ()    
     (Sigma p ((f,x):xs) , Sigma p' ((f',x'):xs')) -> do
           check $ f == f'
           x <: x'
           unif (Bind (synthId f) x' <| g) (Sigma p xs) (Sigma p' xs')
     (Pair _ xs , Pair _ xs') -> eqList (\(f,x) (f',x') -> check (f == f') >> x <: x') xs xs'
     (Proj x f , Proj x' f') -> check (f == f') >> unif g x x'
     (V _ x , V _ x') -> check (x == x')
     (Hole _ _, _) -> constraint
     (_, Hole _ _) -> constraint
     (This,This) -> return ()
     (Tag _ t, Tag _ t') -> check $ t == t'
     (Fin _ ts , Fin _ ts') -> check $ ts == ts'
     (Cas _ _ e xs , Cas _ _ e' xs') -> e <: e' >> eqList (\(f,x) (f',x') -> check (f == f') >> x <: x') xs xs'
     _ | isBox q || isBox q' -> unif' g q' q
     _  -> crash
     where (<:) :: Type -> Type -> Result ()
           (<:) = unif g 
           infix 4 <:
           constraint = report $ vcat (["constraint: " <> display g q',
                                        "equal to: " <> display g q] ++ chkCtx)
           check :: Bool -> Result () 
           check c = unless c crash 
           crash :: Result ()
           crash = throwError (e,hang "type mismatch: " 2 $ vcat 
                               (["type:         " <+> display g q',
                                 "is not sub of:" <+> display g q] ++ chkCtx))
           chkCtx = ["inferred:" <+> display g0 q0',
                     "expected:" <+> display g0 q0 ,
                     "for:" <+> display g0 e ,
                     "context:" <+> dispContext g0]
           eqList p [] [] = return ()
           eqList p (x:xs) (x':xs') = p x x' >> eqList p xs xs'
           eqList p _ _ = crash

cType g e t = cType0 g e =<< whnf g t

-- | Reduce to whnf. May loop if 
whnf g x = do
  -- report $ "whnf: " <> (display g x)
  m <- fst <$> ask
  case whnf' m x of 
    Nothing -> return x
    Just x' -> whnf g x' -- TODO: consume some fuel

-- | One step of reduction to whnf
whnf' :: Term -> Term -> Maybe Term
whnf' m This = Just m
whnf' m (Proj x f) = proj <$> whnf' m x <*> pure f
whnf' m (App  f x) = app  <$> whnf' m f <*> pure x
whnf' m (Ann x t) = Just x
whnf' _ x = Nothing

-- | Will the argument reduce at all if passed to whnf?
isBox x = isJust (whnf' (hole "isBox: dummy") x)

projType e f fs = case break ((==f) . fst) fs of
                    (hs,((_,t):_)) -> Just (([proj e h | (h,_) <- reverse hs] ++ map var [0..]) ∙ t)
                    _ -> Nothing

