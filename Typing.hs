{-# LANGUAGE DoAndIfThenElse #-}
module Typing where

import Common
import Names
import Terms
import NormalForm(NF,Type)
import qualified NormalForm as NF
import Env(Env)
import qualified Env as Env
import qualified Data.Map as M
import qualified Data.Maybe as Maybe
import qualified Data.List as List


checkDec :: Env -> (Ident,Term,Term) -> TypeError (Ident,NF,NF)
checkDec e (i,t,ty) = do
  ty' <- check e ty (NF.sort 10) -- HACK
  t' <- check e t ty'
  return (i,t',ty')

-- | Type checking

check :: Env -> Term -> Type -> TypeError NF

-- Vars
check e (Var i, _) ty = do
  let i_ty = Env.getType e i
  () <- unify e i_ty ty
  return $ NF.var i

-- *ᵢ
check e (Star s , _) ty = do
  () <- unify e (NF.sort $ s + 1) ty
  return (NF.sort s)

-- | Types

-- Π
check e (Pi i s x tyA tyB t , _pos) ty = do
  let eWithx = Env.addContext e x (NF.var tyA)
  tyB' <- check eWithx tyB (NF.sort $ s - 1)

  let tyA_ty = Env.getType e tyA
  () <- assertSubSort e tyA_ty (NF.sort $ s - 1)

  let e_i = Env.addBinding e i (Env.Pi x tyA tyB') (NF.sort s)
  check e_i t ty

-- Σ
check e (Sigma i s x tyA tyB t , _pos) ty = do
  let eWithx = Env.addContext e x (NF.var tyA)
  tyB' <- check eWithx tyB (NF.sort $ s - 1)

  let tyA_ty = Env.getType e tyA
  () <- assertSubSort e tyA_ty (NF.sort $ s - 1)

  let e_i = Env.addBinding e i (Env.Sigma x tyA tyB') (NF.sort s)
  check e_i t ty

-- Fin
check e (Fin i l t , _pos) ty = do
  let eWithi = Env.addBinding e i (Env.Fin l) (NF.sort 1)
  check eWithi t ty

-- | Eliminator

-- let i = f x in <t>
check e (App i f x t, _pos) ty = do
  let fty = Env.getType e f
  (a, tyA, tyB) <- Env.normalizePi e fty
  let tyB' = fmap (a `swapWith` x) tyB

  let xty = Env.getType e x
  () <- unify e xty (NF.Con tyA)

  let eWithi = Env.addBinding e i (Env.App f x) tyB'
  check eWithi t ty




-- let (x,y) = z in <t>
check e (Proj x y z t, _pos) ty = error "check proj"

-- case x { 'tagᵢ → <tᵢ> | i = 1..n }
check e (Case x l, _pos) ty = do
  let fin = map fst l
  let xty = Env.getType e x
  xfin <- Env.normalizeFin e xty
  () <- if unifyFin xfin fin then return ()
      else throw $ Check x xty "Case decomposition is not consistent with the type."
  l' <- mapM checkbranch l
  let l_simp = Maybe.catMaybes l'
  if length l_simp == 1 then
      return $ snd $ head l_simp
  else
      return $ NF.Case x l_simp
    where
      checkbranch (tag,t) =
          let e' = Env.elimTag e x tag in
          if not $ Env.checkTag e x then return Nothing
          else do do { t' <- check e' t ty ; return $ Just (tag,t') }

-- | Introductions

-- let i : S = λx.<t'> in <t>
check e (Lam i ity x t' t, _pos) ty = do
  (a, tyA, tyB) <- Env.normalizePi e (NF.var ity)
  let tyB' = fmap (a `swapWith` x) tyB
  let e_x = Env.addContext e x (NF.Con tyA)
  t_n <- check e_x t' tyB'
  let eWithi = Env.addBinding e i (Env.Lam x t_n) (NF.var ity)
  check eWithi t ty

-- let i : S = (x,y) in <t>
check e (Pair i ity x y t, _pos) ty = error "check pair"

-- let i : T = 'tagᵢ in <t>
check e (Tag i ity tag t, _pos) ty = do
  xfin <- Env.normalizeFin e (NF.var ity)
  () <- if elem tag xfin then return ()
      else throw $ Check i (NF.var ity) "Tag not included in Fin."
  let e_i = Env.addBinding e i (Env.ITag tag) (NF.var ity)
  check e_i t ty


-- | Unification

unify :: Env -> Type -> Type -> TypeError ()

unify e (NF.Con (NF.Var x)) (NF.Con (NF.Var y)) =
    unifyId e x y

unifyId :: Env -> Ident -> Ident -> TypeError ()
unifyId e i i' | Env.areEqual e i i' =
  return ()

unifyId e i i' = do
  d <- Env.toNF e i
  d' <- Env.toNF e i'
  unify e d d'
  -- case (d,d') of
  --   (Env.Star _, _) -> assertSubSort e (NF.var i) (NF.var i')
  --   ( _, Env.Star _) -> assertSubSort e (NF.var i) (NF.var i')

  --   (Env.Alias z, _) -> unifyId e z i'
  --   (_, Env.Alias z) -> unifyId e i z

  --   (Env.Pi x tyA tyB, Env.Pi x' tyA' tyB') -> do
  --     () <- unifyId e tyA tyA'
  --     if x =~ x' then
  --         unify e tyB tyB'
  --     else
  --         unify e tyB (fmap (x' `swapWith` x) tyB')

  --   (Env.Fin l1, Env.Fin l2) ->
  --        if unifyFin l1 l2 then return ()
  --        else throw $ Unification (NF.var i) (NF.var i')

  --   (_,_) -> throw $ Unification (NF.var i) (NF.var i')

unifyFin :: [String] -> [String] -> Bool
unifyFin l1 l2 =
    List.elem l1 $ List.permutations l2 -- We can do better

-- | SubSort

assertSort :: (Sort -> Sort -> Bool) -> Env -> Type -> Type -> TypeError ()
assertSort f e t t' = undefined
    -- do
  -- s <- Env.normalizeSort e t
  -- s' <- Env.normalizeSort e t'
  -- if f s s' then return ()
  -- else throw $ SubSort t t'

assertSubSort :: Env -> Type -> Type -> TypeError ()
assertSubSort = assertSort (<=)

assertBelowSort :: Env -> Type -> Type -> TypeError ()
assertBelowSort = assertSort (<)
