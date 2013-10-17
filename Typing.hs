{-# LANGUAGE DoAndIfThenElse #-}
module Typing where

import Common
import Names
import Terms
import Env(Env,Definition)
import qualified Env as Env


checkDec :: Env -> (Ident,Term,Term) -> TypeError (Env,(Ident,Ident))
checkDec e (_,t,ty) = do
  (e', ity) <- check e ty (Sort 10) -- HACK
  (e'', it) <- check e' t (Ident ity)
  return (e'', (it, ity))

-- | Type checking



check :: Env -> Term -> Type -> TypeError (Env,Ident)


-- Vars
check e (Var i, _) ty = do
  i_ty <- Env.getType e i
  () <- unify e i_ty ty
  return (e, i)

-- *ᵢ
check e (Star i s t , _) ty = do
  eWithi <- Env.addBinding e i (Env.Star s) (Sort (s+1))
  check eWithi t ty

-- | Types

-- Π
check e (Pi i ity x tyA tyB t , _) ty = do
  let ity' = (Below (Ident ity))
  tyA_ty <- Env.getType e tyA
  () <- unify e tyA_ty ity' -- subsorting issue
  eWithx <- Env.addContext e x (Ident tyA)
  _ <- check eWithx tyB ity'
  eWithi <- Env.typePi e i (Ident ity) x tyA tyB
  check eWithi t ty

-- Σ
check e (Sigma i ity x tyA tyB t , _) ty = do
  let ity' = (Below (Ident ity))
  tyA_ty <- Env.getType e tyA
  () <- unify e tyA_ty ity' -- subsorting issue
  eWithx <- Env.addContext e x (Ident tyA)
  _ <- check eWithx tyB ity'
  eWithi <- Env.typeSigma e i (Ident ity) x tyA tyB
  check eWithi t ty

-- Fin
check e (Fin i ity l t , _) ty = do
  s <- Env.normalizeSort e ity
  if s < 1 then
      throw $ Check i ity "Sort smaller than one."
  else do
    eWithi <- Env.typeFin e i (Ident ity) l
    check eWithi t ty

-- | Eliminator

-- let i = f x in <t>

-- let (x,y) = z in <t>

-- case x do { 'tagᵢ → <tᵢ> | i = 1..n }

-- | Introductions

-- let i : S = λx.<t'> in <t>

-- let i : S = (x,y) in <t>

-- let i : T = 'tagᵢ in <t>

-- | Unification


unify :: Env -> Type -> Type -> TypeError ()
unify e t t' = error "unify"

unify' :: Env -> Type -> Ident -> TypeError ()
unify' e t i = unify e t (Ident i)

unifyId :: Env -> Ident -> Ident -> TypeError ()
unifyId e i i' = unify e (Ident i) (Ident i')
