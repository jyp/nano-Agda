module Typing where

import Common
import Names
import Terms
import Env(Env,Definition)
import qualified Env as Env


checkDec :: (Ident,Term,Term) -> TypeError (Env,Ident,Ident)
checkDec = error "checkDec"

-- | Type checking

check :: Env -> Term -> Ident -> TypeError (Env,Ident)

-- Vars
check e (Var i, _) ty = do
    () <- unify' e (Env.getType e i) ty
    return (e, i)

-- *ᵢ
check e (Star i ity t , _) ty = error "checkStar"

-- | Types

-- Π
check e (Pi i ity x tyA tyB t , _) ty = do
  (eWithity',ity') <- Env.addSortBelow e ity
  () <- unify' eWithity' (Env.getType eWithity' tyA) ity'
  eWithxity' <- Env.addContext eWithity' x (Ident tyA)
  _ <- check eWithxity' tyB ity'
  eWithi <- Env.typePi e i (Ident ity) x tyA tyB
  check eWithi t ty

-- Σ
check e (Sigma i ity x tyA tyB t , _) ty = do
  (eWithity',ity') <- Env.addSortBelow e ity
  () <- unify' eWithity' (Env.getType eWithity' tyA) ity'
  eWithxity' <- Env.addContext eWithity' x (Ident tyA)
  _ <- check eWithxity' tyB ity'
  eWithi <- Env.typeSigma e i (Ident ity) x tyA tyB
  check eWithi t ty

-- Fin
check e (Fin i ity l t , _) ty =
  let s = Env.getSort e ity in
  if s < 1 then throw $ Check i ity "Sort smaller than one."
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
