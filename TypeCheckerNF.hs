{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances, GADTs #-}

module TypeCheckerNF where

import Prelude hiding (length)
import Basics
import qualified Terms
import Terms (Term (Ann))
import Display
import Control.Monad.Error
import Data.Char
import Data.Maybe (isJust)
import Control.Monad.Trans.Error (ErrorT, runErrorT)
import Control.Monad.Trans.Writer
import Data.Functor.Identity
import Data.Sequence hiding (replicate)
import Data.Foldable (toList)
import Normal hiding (Term)
import qualified Normal
import Options

instance Error (Term,Doc) where
  strMsg s = (Terms.Hole dummyPosition "strMsg: panic!",text s)

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

displayT :: Context -> Term -> Doc
displayT = Terms.prettyTerm . fmap entryIdent

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
iType g t@(Terms.Star p s)
   =  return (Star s,Star $ above s)  
iType g (Terms.Pi ident tyt tyt')  
   =  do  (ty ,s1) <- iSort g tyt 
          (ty',s2) <- iSort (Bind ident Abstract ty <| g) tyt'
          let o = s1 ⊔ s2
          return (Pi ident ty ty', Star o)
iType g (Terms.Sigma ident tyt tyt')  
   =  do  (ty,s1)  <- iSort g tyt 
          (ty',s2) <- iSort (Bind ident Abstract ty <| g) tyt'
          let o = s1 ⊔ s2
          return (Sigma ident ty ty', Star o)
iType g e@(Terms.Bound _ x) = do
  return $ (val $ value, wkn (x+1) $ typ)
  where val (Direct v) = wkn (x+1) v
        val _ = var x -- We could do eta-expansion here: etaExpand (var x) typ
        Bind _ value typ = g `index` x
        
iType g (Terms.Hole p x) = do
  report $ hang (text ("context of " ++ x ++ " is")) 2 (dispContext g)
  return (hole x, hole ("type of " ++ x))
iType g (e1 Terms.:$: e2)
  =     do  (v1,si) <- iType g e1
            case si of
              Pi _ ty ty' -> do 
                   v2 <- cType g e2 ty
                   return (app v1 v2, subst0 v2 ty') 
              _             ->  throwError (e1,"invalid application")
iType g (Terms.Proj e f) = do
  (v,t) <- iType g e
  search v t
 where search :: NF -> NF -> Result (Value,Type)
       search v (Sigma (Irr (Identifier (_,f'))) ty ty') 
              | f == f' = return (π1,ty)
              | otherwise = search π2 (subst0 π1 ty')
           where 
                 (π1,π2) = (case v of
                             Pair _ x y -> (x,y) -- substitution is useless if the pair is in normal form.
                             _ -> (proj v True (Irr f'),proj v False (Irr f'))  -- This could not happen if eta-expansion were done.
                             ) :: (NF,NF)
       search _ _ = throwError (e,"field not found")

iType g (Terms.Pair ident e1 e2) = do
  (v1,t1) <- iType g e1
  (v2,t2) <- iType (Bind ident (Direct v1) t1 <| g) e2
  return $ (Pair ident v1 (str v2),Sigma ident t1 t2)
-- Note: the above does not infer a most general type: any potential dependency is discarded.

iType g t@(Terms.Lam x (Terms.Hole _ _) e) = throwError (t,"cannot infer type for" <+> displayT g t)
iType g (Terms.Lam x ty e) = do
    (vty,vs) <- iSort g ty
    (ve,t) <- iType (Bind x Abstract vty <| g) e
    return $ (Lam x vty ve, Pi x vty t)

-- | Infer a sort, and normalise
iSort :: Context -> Term -> Result (Type,Sort)
iSort g e = do
  (val,v) <- iType g e
  case v of 
    Star i -> return (val,i)
    Hole h -> do 
         report $ text h <+> "must be a type"
         return $ (hole h, Sort 1)
    _ -> throwError (e,displayT g e <+> "is not a type")

-- | Test if two types are equal.
unify :: Context -> Term -> Type -> Type -> Result ()
unify g e q q' =
         do let ii = length g
                constraint = report $ vcat ["constraint: " <> display g q',
                                            "equal to  : " <> display g q]
            case (q,q') of
              ((Hole _), t) -> constraint
              (t, Hole _) -> constraint
              _ -> unless (q == q') 
                       (throwError (e,hang "type mismatch: " 2 $ vcat 
                                             ["inferred:" <+> display g q',
                                              "expected:" <+> display g q ,
                                              "for:" <+> displayT g e ,
                                              "context:" <+> dispContext g]))

-- | Check the type and normalize
cType :: Context -> Term -> Type -> Result Value
cType g (Terms.Lam name (Terms.Hole _ _) e) (Pi name' ty ty') = do
        e' <- cType (Bind name Abstract ty <| g) e ty'
        return (Lam name ty e') -- the type and binder is filled in.

cType g (Terms.Lam name ty0 e) (Pi name' ty ty')
  =     do (t,_o) <- iSort g ty0
           unify g (Terms.Hole (identPosition name) (show name)) t ty
           e' <- cType (Bind name Abstract ty <| g) e ty'
           return (Lam name ty e')

cType g (Terms.Pair name e1 e2) (Sigma name' ty ty') = do
  -- note that names do not have to match.
  v1 <- cType g e1 ty           
  v2 <- cType (Bind name (Direct v1) ty <| g) e2 (wk $ subst0 v1 ty') 
        -- The above weakening is there because:
        -- * the type contains no occurence of the bound variable after substitution, but
        -- * the context is extended anyway, to bind the name to its value.
  return $ Pair name' v1 (str v2)
  -- note that the pair must use the name of the sigma for the
  -- field. (The context will use the field name provided by the type)

cType g e v 
  =     do (e',v') <- iType g e
           unify g e v v'
           return e'
