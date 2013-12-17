{-# LANGUAGE DoAndIfThenElse #-}
module Typing where

import Common
import Names
import qualified PPrint as P
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

  let e' = Env.elimApp e i f (NF.Var x) tyB'

  case Env.getIntroOpt e f of
    Just (Env.Lam fx ft) -> do
      let ft_x = fmap (fx `swapWith` x) ft
      n <- check e' t ty
      return $ NF.subs n i ft_x
      -- At some point, we should be able to remove this subsitution.

    _ -> do
      n <- check e' t ty
      return $ NF.App i f (NF.Var x) n


-- let (x,y) = z in <t>
check e (Proj x y z t, _pos) ty = do
  let zty = Env.getType e z
  (a,tyA,tyB) <- Env.normalizeSigma e zty
  let tyB' = fmap (a `swapWith` x) tyB

  let e' = Env.elimProj e x y z (NF.Con tyA) tyB'

  case Env.getIntroOpt e z of
    Just (Env.IPair x' y') -> do
      n <- check e' t ty
      return $
        NF.subs' (NF.subs' n x' (NF.Var x)) y' (NF.Var y)
      -- At some point, we should be able to remove this subsitution.

    _ -> do
      n <- check e' t ty
      return $
        NF.Proj x y z n

-- case x { 'tagᵢ → <tᵢ> | i = 1..n }
check e (Case x l, _pos) ty = do
  let fin = map fst l
  let xty = Env.getType e x
  xfin <- Env.normalizeFin e xty
  () <- if unifyFin xfin fin then return ()
      else throwError $ Check x xty "Case decomposition is not consistent with the type."

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
      else throwError $ Check i (NF.var ity) "Tag not included in Fin."
  let e_i = Env.addBinding e i (Env.ITag tag) (NF.var ity)

  n <- check e_i t ty
  return $ NF.subs' n i (NF.Tag tag)

-- | Helpers for Type checking

checkType typeFun e i s x tyA tyB t ty = do
  let e_x = Env.addContext e x (NF.var tyA)
  tyB' <- check e_x tyB (NF.sort s)

  let tyA_ty = Env.getType e tyA
  () <- assertSubSort e tyA_ty (NF.sort s)

  let e_i = Env.addBinding e i (Env.Pi x tyA tyB') (NF.sort s)

  n <- check e_i t ty
  return $ NF.subs' n i (typeFun x (NF.Var tyA) tyB')

-- | Unification

unify :: Env -> Type -> Type -> TypeError ()
unify e t t' = do
  () <- report $ P.text "Unifying"
        P.<+> P.pretty t P.<+> P.text "and" P.<+> P.pretty t' P.<> P.dot
  unifyDir LeftDir e t t'


-- Dir gives the type of the "smallest" type.
-- Allow to factorize unification while having subtyping.
data Dir = LeftDir | RightDir
reverseDir :: Dir -> Dir
reverseDir LeftDir = RightDir
reverseDir RightDir = LeftDir

unifyDir :: Dir -> Env -> Type -> Type -> TypeError ()

-- verify that x == x' (think about nested cases).
unifyDir dir e (NF.Case x l) n' =
  case Env.getIntroOpt e x of
    Just (Env.ITag tag) ->
        unifyDir dir e (Maybe.fromJust $ List.lookup tag l) n'

    _ -> mapM_ checkbranch l
    where
      checkbranch (tag,n) =
          let e' = Env.elimTag e x tag in
          unifyDir dir e' n n'

unifyDir dir e (NF.App y f x n) n' = do
  let fty = Env.getType e f
  (a, _tyA, tyB) <- Env.normalizePi e fty
  let tyB' = NF.subs' tyB a x
  let e' = Env.elimApp e y f x tyB'

  unifyDir dir e' n n'

unifyDir dir e (NF.Proj x y z n) n' = do
  let zty = Env.getType e z
  (a,tyA,tyB) <- Env.normalizeSigma e zty
  let tyB' = fmap (a `swapWith` x) tyB

  let e' = Env.elimProj e x y z (NF.Con tyA) tyB'

  unifyDir dir e' n n'

unifyDir dir e (NF.Con (NF.Var x)) (NF.Con (NF.Var y)) =
    unifyId dir e x y

unifyDir dir e (NF.Con (NF.Var x)) y = do
  dx <- Env.toNF e x
  unifyDir dir e dx y

unifyDir dir e (NF.Con c) (NF.Con c') =
    unifyCon dir e c c'

-- Reverse
unifyDir dir e n@(NF.Con _) n' =
    unifyDir (reverseDir dir) e n' n


-- | For variables.
unifyId :: Dir -> Env -> Ident -> Ident -> TypeError ()
unifyId _ e i i' | Env.areEqual e i i' = return ()
unifyId dir e i i' = do
  d <- Env.toNF e i
  d' <- Env.toNF e i'
  unifyDir dir e d d'

-- | For Constructers
unifyCon :: Dir -> Env -> Con -> Con -> TypeError ()

unifyCon dir e c c' =
  case (c,c') of
    (NF.Var x, _) -> do
        dx <- Env.toNF e x
        unifyDir dir e dx (NF.Con c')
    (_, NF.Var x) -> do
        dx <- Env.toNF e x
        unifyDir dir e (NF.Con c) dx
    (NF.Star s, NF.Star s') ->
        assert $ compareDir s s'
    (NF.Fin l, NF.Fin l') ->
        assert $ unifyFin l l'
    (NF.Pair c1 c2, NF.Pair c1' c2') -> do
        () <- unifyCon dir e c1 c1'
        unifyCon dir e c2 c2'
    (NF.Tag t, NF.Tag t') ->
        assert $ t == t'
    (NF.Lam x n, NF.Lam x' n') ->
        unifyDir dir e n (fmap (x' `swapWith` x) n')
    (NF.Pi a tyA tyB, NF.Pi a' tyA' tyB') ->
        unifyTypes dir e (a,tyA,tyB) (a',tyA',tyB')
    (NF.Sigma a tyA tyB, NF.Sigma a' tyA' tyB') ->
        unifyTypes dir e (a,tyA,tyB) (a',tyA',tyB')
    (_,_) -> failUni
  where
    failUni :: TypeError ()
    failUni = throwError $ Unification (NF.Con c) (NF.Con c')
    assert b = if b then return () else failUni
    compareDir = case dir of
                LeftDir -> (<=)
                RightDir -> (>=)

-- | Utilities for unification

unifyTypes :: Dir -> Env -> (Ident,Con,NF) -> (Ident,Con,NF) -> TypeError ()
unifyTypes dir e (a,tyA,tyB) (a',tyA',tyB') = do
  () <- unifyCon dir e tyA tyA'
  unifyDir dir e tyB (fmap (a' `swapWith` a) tyB')

unifyFin :: [String] -> [String] -> Bool
unifyFin l1 l2 =
    List.sort l1 == List.sort l2


-- | SubSort

assertSort :: (Sort -> Sort -> Bool) -> Env -> Type -> Type -> TypeError ()
assertSort f e t t' = do
  s <- Env.normalizeSort e t
  s' <- Env.normalizeSort e t'
  if f s s' then return ()
  else throwError $ SubSort t t'

assertSubSort :: Env -> Type -> Type -> TypeError ()
assertSubSort = assertSort (<=)

assertBelowSort :: Env -> Type -> Type -> TypeError ()
assertBelowSort = assertSort (<)
