{-# LANGUAGE DoAndIfThenElse #-}
module Typing where

import Common
import Names
import Terms
import NormalForm(NF,Con,Type)
import qualified NormalForm as NF
import Env(Env)
import qualified Env as Env
import qualified Data.Map as M
import qualified Data.Maybe as Maybe
import qualified Data.List as List
import Control.Monad(foldM)


checkDecs :: Env -> [(Ident,Term,Term)] -> TypeError Env
checkDecs env l =
    let f e def = do
          (i,t,ty) <- checkDec e def
          return $ Env.addBinding e i (Env.Def t) ty
    in
    foldM f env l

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
  return $ NF.sort s

-- | Types

-- Π
check e (Pi i s x tyA tyB t , _) ty =
  checkType NF.Pi e i s x tyA tyB t ty

-- Σ
check e (Sigma i s x tyA tyB t , _) ty =
  checkType NF.Sigma e i s x tyA tyB t ty

-- Fin
check e (Fin i l t , _pos) ty = do
  let e_i = Env.addBinding e i (Env.Fin l) (NF.sort 1)

  n <- check e_i t ty
  return $ NF.subs' n i (NF.Fin l)

-- | Eliminator

-- let i = f x in <t>
check e (App i f x t, _pos) ty = do
  let fty = Env.getType e f
  (a, tyA, tyB) <- Env.normalizePi e fty
  let tyB' = fmap (a `swapWith` x) tyB

  let xty = Env.getType e x
  () <- unify e xty (NF.Con tyA)

  case Env.getIntroOpt e f of
    Just (Env.Lam fx ft) -> do
      let ft_x = fmap (fx `swapWith` x) ft
          e_i = Env.addBinding e i (Env.Def ft_x) tyB'
      n <- check e_i t ty
      return $ NF.subs n i ft_x

    _ -> do
      let e_i = Env.addBinding e i (Env.App f x) tyB'
      n <- check e_i t ty
      return $ NF.App i f (NF.Var x) n


-- let (x,y) = z in <t>
check e (Proj x y z t, _pos) ty = do
  let zty = Env.getType e z
  (a,tyA,tyB) <- Env.normalizeSigma e zty
  let tyB' = fmap (a `swapWith` x) tyB

  case Env.getIntroOpt e z of
    Just (Env.IPair x' y') -> do
      let e_x = Env.addAlias e x' x
      let e_xy = Env.addAlias e_x y' y
      n <- check e_xy t ty
      return $
        NF.subs' (NF.subs' n x' (NF.Var x)) y' (NF.Var y)

    _ -> do
      let e_z = Env.addElim e z (Env.EPair x y)
          e_zx = Env.addContext e_z x (NF.Con tyA)
          e_zxy = Env.addContext e_zx y tyB'
      n <- check e_zxy t ty
      return $
        NF.Proj x y z n

-- case x { 'tagᵢ → <tᵢ> | i = 1..n }
check e (Case x l, _pos) ty = do
  let fin = map fst l
  let xty = Env.getType e x
  xfin <- Env.normalizeFin e xty
  () <- if unifyFin xfin fin then return ()
      else throw $ Check x xty "Case decomposition is not consistent with the type."

  case Env.getIntroOpt e x of
    Just (Env.ITag tag) ->
        check e (Maybe.fromJust $ List.lookup tag l) ty

    _ -> do
      l' <- mapM checkbranch l
      return $ NF.Case x l'
    where
      checkbranch (tag,t) =
          let e' = Env.elimTag e x tag in
          do { t' <- check e' t ty ; return (tag,t') }

-- | Introductions

-- let i : S = λx.<t'> in <t>
check e (Lam i ity x t' t, _pos) ty = do
  (a, tyA, tyB) <- Env.normalizePi e (NF.var ity)
  let tyB' = fmap (a `swapWith` x) tyB
  let e_x = Env.addContext e x (NF.Con tyA)
  t_n <- check e_x t' tyB'
  let e_i = Env.addBinding e i (Env.Lam x t_n) (NF.var ity)

  n <- check e_i t ty
  return $ NF.subs' n i (NF.Lam x t_n)

-- let i : S = (x,y) in <t>
check e (Pair i ity x y t, _pos) ty = do
  (a, tyA, tyB) <- Env.normalizeSigma e (NF.var ity)

  _x_n <- check e (var x) (NF.Con tyA)

  let tyB' = fmap (a `swapWith` x) tyB
  let e_x = Env.addContext e x (NF.Con tyA)
  _y_n <- check e_x (var y) tyB'

  let e_i = Env.addBinding e i (Env.IPair x y) (NF.var ity)

  n <- check e_i t ty
  return $ NF.subs' n i (NF.Pair (NF.Var x) (NF.Var y))

-- let i : T = 'tagᵢ in <t>
check e (Tag i ity tag t, _pos) ty = do
  xfin <- Env.normalizeFin e (NF.var ity)
  () <- if elem tag xfin then return ()
      else throw $ Check i (NF.var ity) "Tag not included in Fin."
  let e_i = Env.addBinding e i (Env.ITag tag) (NF.var ity)

  n <- check e_i t ty
  return $ NF.subs' n i (NF.Tag tag)

-- | Helpers for Type checking

checkType typeFun e i s x tyA tyB t ty = do
  let e_x = Env.addContext e x (NF.var tyA)
  tyB' <- check e_x tyB (NF.sort $ s - 1)

  let tyA_ty = Env.getType e tyA
  () <- assertSubSort e tyA_ty (NF.sort $ s - 1)

  let e_i = Env.addBinding e i (Env.Pi x tyA tyB') (NF.sort s)

  n <- check e_i t ty
  return $ NF.subs' n i (typeFun x (NF.Var tyA) tyB')

-- | Unification

unify :: Env -> Type -> Type -> TypeError ()

unify e (NF.Con (NF.Var x)) (NF.Con (NF.Var y)) =
    unifyId e x y

unify e (NF.Con (NF.Var x)) y = do
  dx <- Env.toNF e x
  unify e dx y

unify e x (NF.Con (NF.Var y)) = do
  dy <- Env.toNF e y
  unify e x dy

unify e (NF.Con c) (NF.Con c') =
    unifyCon e c c'

unify e n@(NF.Case x l) n'@(NF.Case x' l') = do
  let fin = map fst l
      fin' = map fst l'
  (ls, ls') <-
    if unifyFin fin fin' then
        return (sortFst l, sortFst l')
    else throw $ Unification n n'
  mapM_ uniCase $ zip ls ls'
      where sortFst = List.sortBy (\ a b -> compare (fst a) (fst b))
            uniCase (ns,ns') =
                unify e (snd ns) (fmap (x' `swapWith` x) $ snd ns')

unify e (NF.App x f y n) (NF.App x' f' y' n') = do
  () <- unifyCon e y y'
  unify e n (fmap ((x' `swapWith` x) . (f' `swapWith` f)) n')
  -- It should work fine, but I have a bad presentiment.

unify e (NF.Proj x y z n) (NF.Proj x' y' z' n') = do
  unify e n (fmap swap n')
      where swap =
                (x' `swapWith` x) .
                (y' `swapWith` y) .
                (z' `swapWith` z)

-- Catch all
unify _e n n' = throw $ Unification n n'


-- | For variables.
unifyId :: Env -> Ident -> Ident -> TypeError ()
unifyId e i i' | Env.areEqual e i i' = return ()
unifyId e i i' = do
  d <- Env.toNF e i
  d' <- Env.toNF e i'
  unify e d d'

-- | For Constructers
unifyCon :: Env -> Con -> Con -> TypeError ()

unifyCon e c c' =
  case (c,c') of
    (NF.Var x, _) -> do
        dx <- Env.toNF e x
        unify e dx (NF.Con c')
    (_, NF.Var x) -> do
        dx <- Env.toNF e x
        unify e (NF.Con c) dx
    (NF.Star s, NF.Star s') ->
        assert $ s <= s'
    (NF.Fin l, NF.Fin l') ->
        assert $ unifyFin l l'
    (NF.Pair c1 c2, NF.Pair c1' c2') -> do
        () <- unifyCon e c1 c1'
        unifyCon e c2 c2'
    (NF.Tag t, NF.Tag t') ->
        assert $ t == t'
    (NF.Lam x n, NF.Lam x' n') ->
        unify e n (fmap (x' `swapWith` x) n')
    (NF.Pi a tyA tyB, NF.Pi a' tyA' tyB') ->
        unifyTypes e (a,tyA,tyB) (a',tyA',tyB')
    (NF.Sigma a tyA tyB, NF.Pi a' tyA' tyB') ->
        unifyTypes e (a,tyA,tyB) (a',tyA',tyB')
    (_,_) -> failUni
  where
    failUni :: TypeError ()
    failUni = throw $ Unification (NF.Con c) (NF.Con c')
    assert b = if b then return () else failUni

-- | Utilities for unification

unifyTypes :: Env -> (Ident,Con,NF) -> (Ident,Con,NF) -> TypeError ()
unifyTypes e (a,tyA,tyB) (a',tyA',tyB') = do
  () <- unifyCon e tyA tyA'
  unify e tyB (fmap (a' `swapWith` a) tyB')

unifyFin :: [String] -> [String] -> Bool
unifyFin l1 l2 =
    List.sort l1 == List.sort l2


-- | SubSort

assertSort :: (Sort -> Sort -> Bool) -> Env -> Type -> Type -> TypeError ()
assertSort f e t t' = do
  s <- Env.normalizeSort e t
  s' <- Env.normalizeSort e t'
  if f s s' then return ()
  else throw $ SubSort t t'

assertSubSort :: Env -> Type -> Type -> TypeError ()
assertSubSort = assertSort (<=)

assertBelowSort :: Env -> Type -> Type -> TypeError ()
assertBelowSort = assertSort (<)
