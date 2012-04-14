{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances, GADTs, TupleSections #-}

module TypeCheckerNF where

import Prelude hiding (length)
import Basics
import Display
import Control.Monad.Error
import Data.Char
import Data.Maybe (isJust)
import Control.Monad.Trans.Error (ErrorT, runErrorT)
import Control.Monad.Trans.Writer
import Data.Functor.Identity
import Data.Sequence hiding (replicate,zip,reverse)
import Data.Foldable (toList)
import Normal 
import qualified Normal
import Options

instance Error (Term,Doc) where
  strMsg s = (hole "strMsg: panic!",text s)

type Result a = (ErrorT (Term,Doc)) -- term is used for position information
                (WriterT [Doc] Identity) a

report :: Doc -> Result ()
report x = lift $ tell [x]

runChecker :: Result a -> (Either (Term,Doc) a,[Doc])
runChecker x = runIdentity $ runWriterT $ runErrorT x

data Definition = Abstract -- ^ lambda, pi, sigma bound
                | Direct Value -- ^ pair bound

type Value    = NF
type Type     = Value
data Bind     = Bind {entryIdent :: Ident, 
                      entryValue :: Definition, -- ^ Value for identifier. 
                      entryType :: Type   -- ^ Attention: context of the type does not contain the variable bound here.
                     }
type Context  = Seq Bind

display :: Context -> NF -> Doc
display c = prettyTerm (fmap entryIdent c)

dispContext :: Context -> Doc
dispContext ctx = case viewl ctx of
  EmptyL -> mempty
  Bind x val typ :< ctx' -> let di = display ctx' in (case val of
    Abstract   ->             pretty x <+>                             ":" <+> di typ
    Direct   v ->             pretty x <+> sep ["=" <+> parens (di v), ":" <+> di typ]
    ) $$ dispContext ctx'

-- FIXME: flag an error if impredicativity disabled and we use it anyway.

-- | Infer a type and evaluate to normal form
iType :: Context -> Term -> Result (Value,Type)
iType g (Ann e tyt)
  =     do  (ty,o) <- iSort g tyt 
            v <- cType g e ty
            return (v,ty) -- type annotations are removed
iType g t@(Star p s)
   =  return (star s,star $ above s)  
iType g (Pi ident tyt tyt')  
   =  do  (ty ,s1) <- iSort g tyt 
          (ty',s2) <- iSort (Bind ident Abstract ty <| g) tyt'
          let o = s1 ⊔ s2
          return (Pi ident ty ty', star o)
iType g (Sigma _ []) = return (sigma [],star 0)          
iType g (Sigma _ ((f,t):ts))  
   =  do  (t',s1)  <- iSort g t 
          (Sigma _ ts',s2) <- iSort (Bind (synthId f) Abstract t' <| g) (sigma ts)
          let o = s1 ⊔ s2          
          return (sigma ((f,t'):ts'), star o)
iType g e@(V _ x) = do
  return $ (val $ value, wkn (x+1) ∙ typ)
  where val (Direct v) = wkn (x+1) ∙ v
        val _ = var x -- We could do eta-expansion here: etaExpand (var x) typ
        Bind _ value typ = g `index` x
        
iType g (Hole p x) = do
  report $ hang (text ("context of " ++ x ++ " is")) 2 (dispContext g)
  return (hole x, hole ("type of " ++ x))

iType g t@(Lam x (Hole _ _) e) = throwError (t,"cannot infer type for" <+> display g t)
iType g (Lam x ty e) = do
    (vty,vs) <- iSort g ty
    (ve,t) <- iType (Bind x Abstract vty <| g) e
    return $ (Lam x vty ve, Pi x vty t)

iType g (Pair _ fs) = do
  (fs,vs,ts) <- unzip3 <$> (forM fs $ \(f,x) -> do 
                            (x',xt) <- iType g x
                            return (f,x',xt))
  return (pair (zip fs vs),sigma (zip fs [ wkn n ∙ t | (n,t) <- zip [0..] ts])) 
  -- possible dependencies in the type are not discovered 
  
iType g e | Just e' <- evaluate e = iType g =<< comput g e e'
  
iType g (App e1 e2)
  =     do  (v1,si) <- iType g e1
            case si of
              Pi _ ty ty' -> do 
                   v2 <- cType g e2 ty
                   return (app v1 v2, subst0 v2 ∙ ty') 
              _             ->  throwError (e1,"invalid application")

iType g (Proj e f) = do
  (e',et) <- iType g e
  case et of 
    Sigma _ fs -> case break ((==f) . fst) fs of
      (hs,((_,t):_)) -> do
        let tt = apply ([proj e h | (h,_) <- reverse hs] ++ map var [0..]) t
        return (proj e f,tt)
      _ -> throwError (e,"field" <+> text f <+> "not found in type" <+> display g et)
    _ -> throwError (e,"type should be record:" <+> display g et)
    

iType g t = throwError (t,"cannot infer type for" <+> display g t)
         
-- | Infer a sort, and normalise
iSort :: Context -> Term -> Result (Type,Sort)
iSort g e = do
  (val,v) <- iType g e
  case v of 
    Star _ i -> return (val,i)
    Hole _ h -> do 
         report $ text h <+> "must be a type"
         return $ (hole h, Sort 1)
    _ -> throwError (e,display g e <+> "is not a type")

-- | Test if two types are equal.
unify :: Context -> Term -> Type -> Type -> Result ()
unify g e q q' =
         do let ii = length g
                constraint = report $ vcat ["constraint: " <> display g q',
                                            "equal to  : " <> display g q]
            case (q,q') of
              ((Hole _ _), t) -> constraint
              (t, Hole _ _) -> constraint
              _ -> unless (q == q') 
                       (throwError (e,hang "type mismatch: " 2 $ vcat 
                                             ["inferred:" <+> display g q',
                                              "expected:" <+> display g q ,
                                              "for:" <+> display g e ,
                                              "context:" <+> dispContext g]))

-- | Check the type and normalize
cType :: Context -> Term -> Type -> Result Value
cType g (Lam name (Hole _ _) e) (Pi name' ty ty') = do
        e' <- cType (Bind name Abstract ty <| g) e ty'
        return (Lam name ty e') -- the type and binder is filled in.

cType g (Lam name ty0 e) (Pi name' ty ty')
  =     do (t,_o) <- iSort g ty0
           unify g (Hole (identPosition name) (show name)) t ty
           e' <- cType (Bind name Abstract ty <| g) e ty'
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
    Pair _ xs' <- cType g (pair xs) (subst0 x ∙ sigma xts)
    return (pair ((f,x'):xs'))

-- cType g (Box name e _) et = do
--   e' <- cType (Bind name (Direct (Box name e (map var [0..]))) et <| g) e et -- FIXME: env.
--   return (Box name e' $ map var [0..])-- FIXME: env.
  
cType g (Proj e f) t = do
  e' <- cType g e (sigma [(f,t)])
  return (proj e' f)
  
  
cType g e v | Just v' <- evaluate v = cType g e =<< comput g v v'
cType g e v | Just e' <- evaluate e = (\x -> cType g x v) =<< comput g e e'

cType g e v = do 
  (e',v') <- iType g e
  unify g e v v'
  return e'

comput g x y = do 
  report $ display g x <> "  -->  " <> display g y
  return y