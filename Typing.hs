{-# LANGUAGE DoAndIfThenElse #-}
module Typing where

import Common
import Names
import Terms
import Env(Env)
import qualified Env as Env
import qualified Data.Map as M


checkDec :: Env -> (Ident,Term,Term) -> TypeError (Env,(Ident,Ident,Ident))
checkDec e (i,t,ty) = do
  (e', ity) <- check e ty (Sort 10) -- HACK
  (e'', it) <- check e' t (Ident ity)
  e_i <- Env.addBinding e'' i (Env.Alias it) (Ident ity)
  return (e_i, (i, it, ity))

-- | Type checking



assertSort :: (Sort -> Sort -> Bool) -> Env -> Type -> Type -> TypeError ()
assertSort f e t t' = do
  s <- Env.normalizeSort' e t
  s' <- Env.normalizeSort' e t'
  if f s s' then return ()
  else throw $ SubSort t t'

assertSubSort :: Env -> Type -> Type -> TypeError ()
assertSubSort = assertSort (<=)

assertBelowSort :: Env -> Type -> Type -> TypeError ()
assertBelowSort = assertSort (<)

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
  tyA_ty <- Env.getType e tyA
  () <- assertSubSort e tyA_ty (Ident ity)
  eWithx <- Env.addContext e x (Ident tyA)
  tyB_n <- check eWithx tyB (Ident ity)
  eWithi <- Env.typePi e i (Ident ity) x tyA tyB_n
  check eWithi t ty

-- Σ
check e (Sigma i ity x tyA tyB t , _) ty = do
  tyA_ty <- Env.getType e tyA
  () <- assertSubSort e tyA_ty (Ident ity)
  eWithx <- Env.addContext e x (Ident tyA)
  tyB_n <- check eWithx tyB (Ident ity)
  eWithi <- Env.typeSigma e i (Ident ity) x tyA tyB_n
  check eWithi t ty

-- Fin
check e (Fin i ity l t , _) ty = do
  () <- assertSubSort e (Sort 1) (Ident ity)
  eWithi <- Env.typeFin e i (Ident ity) l
  check eWithi t ty

-- | Eliminator

-- let i = f x in <t>
check e (App i f x t, _) ty = error "check app"

-- let (x,y) = z in <t>
check e (Proj x y z t, _) ty = error "check proj"

-- case x { 'tagᵢ → <tᵢ> | i = 1..n }
check e (Case x l, _) ty = error "check case"

-- | Introductions

-- let i : S = λx.<t'> in <t>
check e (Lam i ity x t' t, _) ty = do
  (a, tyA, (etyB,tyB)) <- Env.normalizePi e ity
  let (e', tyB') = Env.instanciate e a (etyB,tyB) x
  e'Withx <- Env.addContext e' x (Ident tyA)
  t_n <- check e'Withx t' (Ident tyB')
  eWithi <- Env.addBinding e i (Env.Lam x t_n) (Ident ity)
  check eWithi t ty

-- let i : S = (x,y) in <t>
check e (Pair i ity x y t, _) ty = error "check pair"

-- let i : T = 'tagᵢ in <t>
check e (Tag i ity tag t, _) ty = error "check tag"

-- | Unification

unify :: Env -> Type -> Type -> TypeError ()
unify e t t' =
    case t' of
      Ident i' -> unify' e t i'
      Sort _ -> assertSubSort e t t'

unify' :: Env -> Type -> Ident -> TypeError ()
unify' e t i =
    case t of
      Ident i' -> unifyId e i' i
      Sort _ -> assertSubSort e t (Ident i)

unifyId :: Env -> Ident -> Ident -> TypeError ()
unifyId e id id' | Env.areEqual e id id' =
  return ()
unifyId e i i' = do
  d <- e Env.! i
  d' <- e Env.! i'
  case (d,d') of
    (Env.Star _, _) -> assertSubSort e (Ident i) (Ident i')
    ( _, Env.Star _) -> assertSubSort e (Ident i) (Ident i')

    (Env.Alias z, _) -> unifyId e z i'
    (_, Env.Alias z) -> unifyId e i z

    (Env.Pi x tyA (eB,tyB), Env.Pi x' tyA' (eB',tyB')) -> do
      () <- unifyId e tyA tyA'
      if x =~ x' && tyB =~ tyB' && eB == eB' then
          return ()
      else do
        let Env.Env c ei ee = e Env.∪ eB Env.∪ eB'
        e' <- Env.addAlias e x x'
        unifyId e' tyB tyB'

    (_,_) -> throw $ Unification (Ident i) (Ident i')
