{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances, GADTs, TupleSections #-}

module TypeCheckerNF where

import Prelude hiding (length)
import Basics
import Display
import Control.Monad.Error
import Data.Maybe
import Control.Monad.Trans.Error (ErrorT, runErrorT)
import Control.Monad.Trans.Writer
import Data.Functor.Identity
import Data.Sequence hiding (replicate,zip,reverse)
import Data.Foldable (toList)
import Normal 
import Options

instance Error (Term,Doc) where
  strMsg s = (hole "strMsg: panic!",text s)

type Result a = (ErrorT (Term,Doc)) -- term is used for position information
                (WriterT [Doc] Identity) a

report :: Doc -> Result ()
report x = lift $ tell [x]

runChecker :: Result a -> (Either (Term,Doc) a,[Doc])
runChecker x = runIdentity $ runWriterT $ runErrorT x

type Value    = NF
type Type     = Value
data Bind     = Bind {entryIdent :: Ident, 
                      entryType :: Type   -- ^ Attention: context of the type does not contain the variable bound here.
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
iType g t@(Star p s) =  return (star s,star $ above s)  
iType g (Pi ident tyt tyt')  = do
    (ty ,s1) <- iSort g tyt 
    (ty',s2) <- iSort (Bind ident ty <| g) tyt'
    let o = s1 ⊔ s2
    return (Pi ident ty ty', star o)
iType g (Sigma i []) = return (Sigma i [],star 0)          
iType g (Sigma i ((f,t):ts)) = do
   (t',s1)  <- iSort g t 
   (Sigma _ ts',s2) <- iSort (Bind (synthId f)  t' <| g) (sigma ts)
   let o = s1 ⊔ s2          
   return (Sigma i ((f,t'):ts'), star o)
iType g e@(V _ x) = do
  return $ (var x, wkn (x+1) ∙ typ)
  where Bind _ typ = g `index` x
        
iType g (Hole p x) = do
  report $ hang (text ("context of " ++ x ++ " is")) 2 (dispContext g)
  return (hole x, hole ("type of " ++ x))

iType g t@(Lam x (Hole _ _) e) = throwError (t,"cannot infer type for" <+> display g t)
iType g (Lam x ty e) = do
    (vty,vs) <- iSort g ty
    (ve,t) <- iType (Bind x  vty <| g) e
    return $ (Lam x vty ve, Pi x vty t)

iType g (Pair _ fs) = do
  (fs,vs,ts) <- unzip3 <$> (forM fs $ \(f,x) -> do 
                            (x',xt) <- iType g x
                            return (f,x',xt))
  return (pair (zip fs vs),sigma (zip fs [ wkn n ∙ t | (n,t) <- zip [0..] ts])) 
  -- possible dependencies in the type are not discovered 
  
iType g (Tag t) = return (Tag t,Fin [t])
iType g (Fin ts) = return (Fin ts,star 0)
  
iType g (App e1 e2) = do
   (e1',et) <- iType g e1
   et' <- open g et
   case et' of
     Pi _ ty ty' -> do 
          v2 <- cType g e2 ty
          return (app e1' v2, subst0 v2 ∙ ty') 
     _             ->  throwError (e1,"type should be function:" <> display g et')

iType g (Proj e f) = do
  (e',et) <- iType g e
  et' <- open g et
  case et' of 
    Sigma _ fs -> case projType e f fs of
                    Just tt -> return (proj e f,tt)
                    _ -> throwError (e,"field" <+> text f <+> "not found in type" <+> display g et')
    _ -> throwError (e,hang "expected record:" 2 $ sep ["term:" <+> display g e,
                                                        "type:" <+> display g et',
                                                        "field:" <+> text f])
    
iType g (Box n t e) = do
  (t',_) <- iSort g t
  return (Box n t' e,t')
  -- checking inside the box is delayed until one needs to compare its content to something else.

iType g t = throwError (t,hang "cannot infer type for" 2 $ display g t)
         
-- | Infer a sort, and normalise
iSort :: Context -> Term -> Result (Type,Sort)
iSort g e = do
  (val,v) <- iType g e
  v' <- open g v
  case v' of 
    Star _ i -> return (val,i)
    Hole _ h -> do 
         report $ text h <+> "must be a type"
         return $ (hole h, Sort 1)
    _ -> throwError (e,display g e <+> "is not a type")


-- | Check the type and normalize
cType :: Context -> Term -> Type -> Result Value
cType g (Lam name (Hole _ _) e) (Pi name' ty ty') = do
        e' <- cType (Bind name ty <| g) e ty'
        return (Lam name ty e') -- the type and binder is filled in.

cType g (Lam name ty0 e) (Pi name' ty ty')
  =     do (t,_o) <- iSort g ty0
           unify g (Hole (identPosition name) (show name)) ty t
           e' <- cType (Bind name ty <| g) e ty'
           return (Lam name ty e')

cType g (Pair _ ignored) (Sigma _ []) = return $ pair ignored
-- note: subtyping
cType g (Pair _ ((f,x):xs)) (Sigma i fs@((f',xt):xts)) 
-- BETTER: directly lookup the field in the pair instead.
  | f /= f' = do  Pair _ fs' <- cType g (pair xs) (sigma fs)
                  return $ pair ((f,x):fs')
  | f == f' = do
    -- note that names do not have to match.  
    x' <- cType g x xt
    report $ hang "Remains to check: " 2 $ sep ["pair:" <+> display g (pair xs), 
                                                "type:" <+>  display g (subst0 x' ∙ sigma xts)]
    Pair _ xs' <- cType g (pair xs) (subst0 x' ∙ sigma xts)
    return (pair ((f,x'):xs'))

cType g (Cas c cs) t = do
  let ct = Fin $ map fst cs
  c' <- cType g c ct
  cs' <- forM cs $ \ (p,v) -> do
     v' <- cType g v t
     return (p,v')
  return (cas c' cs')
  
cType g e box | isBox box = cType g e =<< open g box

cType g e v = do 
  -- report $ hang "no checking rule for" 2 $ vcat ["term = " <> display g e, "type = " <>display g v]
  (e',v') <- iType g e
  unify g e v' v
  return e'

-- | Subtyping test
unify :: Context -> Term -> Type -> Type -> Result ()
unify g0 e q0' q0 = unif g0 q0' q0 where 
   unif :: Context -> Type -> Type -> Result ()
   unif g q' q = case (q',q) of
     (Star _ s , Star _ s') -> check $ s == s'
     (Pi i a b , Pi _ a' b') -> (a' <: a) >> unif (Bind i a <| g) b b'
     (Lam i a b , Lam _ a' b') -> (a' <: a) >> unif (Bind i a <| g) b b'
     (App a b , App a' b') -> (a <: a') >> (b <: b')
     (Sigma _ xs, Sigma _ []) -> return ()    
     (Sigma _ ((f,x):xs) , Sigma _ ((f',x'):xs')) -> do
           check $ f == f'
           x <: x'
           unif (Bind (synthId f) x' <| g) (sigma xs) (sigma xs')
     (Pair _ xs , Pair _ xs') -> eqList (\(f,x) (f',x') -> check (f == f') >> x <: x') xs xs'
     (Proj x f , Proj x' f') -> x <: x' >> check (f == f')
     (V _ x , V _ x') -> check (x == x')
     (Hole _ _, _) -> constraint
     (_, Hole _ _) -> constraint
     (Box _ t e , Box _ t' e') -> t <: t' >> e <: e'
     (Tag t  , Tag t') -> check $ t == t'
     (Fin ts , Fin ts') -> check $ all (`elem` ts') ts
     (Cas x xs , Cas x' xs') -> x <: x' >> eqList (\(f,x) (f',x') -> check (f == f') >> x <: x') xs xs'
     _ | isBox q' -> do
       x' <- open g q' 
       x' <: q
     _ | isBox q -> do
       x <- open g q 
       x <: q'
     (Ann x _ , x') -> x <: x' -- FIXME: annotations should not be found in NFs; remove this.
     (x , Ann x' _) -> x <: x'
     _  -> crash
     where (<:) :: Type -> Type -> Result ()
           (<:) = unif g
           infix 4 <:
           constraint = report $ vcat (["constraint: " <> display g q',
                                        "subtype of: " <> display g q] ++ chkCtx)
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

uncheckedOpen box@(Box i t e) = (subst0 box ∙ e) `ann` t
uncheckedOpen x = x

open g box = case evaluate box of
               Just (o,t) -> do
                 report (hang "opening:" 2 $ sep ["box:" <+> display g box, 
                                                  "in: " <+> display g o,
                                                  "typ:" <+> display g t]) 
                 cType g o t 
               _ -> return box


projType e f fs = case break ((==f) . fst) fs of
                    (hs,((_,t):_)) -> Just (([proj e h | (h,_) <- reverse hs] ++ map var [0..]) ∙ t)
                    _ -> Nothing


isBox = isJust . evaluate

evaluate :: Term -> Maybe (Term,Type)
evaluate box@(Box _ t e) = return (subst0 box ∙ e,t)
evaluate (Proj x f) | Just (x',Sigma _ fs) <- evaluate x, Just tt <- projType x' f fs = Just (proj x' f, tt)
evaluate (App f x) | Just (f',Pi _ _ b) <- evaluate f = Just (f' `app` x, subst0 x ∙ b)
-- evaluate (Cas x cs) = (`cas` cs) <$> evaluate x 
-- FIXME: do it.
evaluate _ = Nothing
