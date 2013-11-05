{-# LANGUAGE DoAndIfThenElse #-}
module Typing where

import Common
import Names
import Terms
import Env(Env)
import qualified Env as Env
import qualified Data.Map as M
import qualified Data.Maybe as Maybe
import qualified Data.List as List


checkDec :: Env -> (Ident,Term,Term) -> TypeError (Env,(Ident,Ident,Ident))
checkDec e (i,t,ty) = do
  (e', ity) <- check e ty (Sort 10) -- HACK
  (e'', it) <- check e' t (Ident ity)
  let e_i = Env.addBinding e'' i (Env.Alias it) (Ident ity)
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
check e (Star i s t , _) ty =
  let eWithi = Env.addBinding e i (Env.Star s) (Sort (s+1))
  in check eWithi t ty

-- | Types

-- Π
check e (Pi i ity x tyA tyB t , _) ty = do
  s <- Env.normalizeSort e ity

  let eWithx = Env.addContext e x (Ident tyA)
  tyB' <- check eWithx tyB (Sort $ s - 1)

  tyA_ty <- Env.getType e tyA
  () <- assertSubSort e tyA_ty (Sort $ s - 1)

  let eWithi =
          Env.addBinding e i (Env.Pi x tyA tyB') (Ident ity)
  check eWithi t ty

-- Σ
check e (Sigma i ity x tyA tyB t , _) ty = do
  s <- Env.normalizeSort e ity

  let eWithx = Env.addContext e x (Ident tyA)
  tyB' <- check eWithx tyB (Sort $ s - 1)

  tyA_ty <- Env.getType e tyA
  () <- assertSubSort e tyA_ty (Sort $ s - 1)

  let eWithi =
          Env.addBinding e i (Env.Sigma x tyA tyB') (Ident ity)
  check eWithi t ty

-- Fin
check e (Fin i ity l t , _) ty = do
  () <- assertSubSort e (Sort 1) (Ident ity)
  let eWithi = Env.addBinding e i (Env.Fin l) (Ident ity)
  check eWithi t ty

-- | Eliminator

-- let i = f x in <t>
check e (App i f x t, _) ty = do
  fty <- Env.getType e f
  (a, tyA, (etyB,tyB)) <- Env.normalizePi e fty
  let (e', tyB') = Env.instanciate e a (etyB,tyB) x

  xty <- Env.getType e x
  () <- unify e xty (Ident tyA)

  let eWithi = Env.addBinding e i (Env.App f x) (Ident tyB')
  check eWithi t ty




-- let (x,y) = z in <t>
check e (Proj x y z t, _) ty = error "check proj"

-- case x { 'tagᵢ → <tᵢ> | i = 1..n }
check e (Case x l, _) ty = do
  let fin = map fst l
  xty <- Env.getType e x
  xfin <- Env.normalizeFin e xty
  () <- if unifyFin xfin fin then return ()
      else throw $ Check x xty "Case decomposition is not consistent with the type."
  l <- mapM checkbranch l
  return $ head $ Maybe.catMaybes l
  -- I have no idea how to return the multiple branchs of the case in the format (env, var). I know there is always at least one branch so I'm returning the first one. This should be enough for most typechecking purposes.
      where
        checkbranch (tag,t) =
            let e' = Env.elimTag e x tag in
            if not $ Env.checkTag e x then return Nothing
            else do check e' t ty >>= return . Just




-- | Introductions

-- let i : S = λx.<t'> in <t>
check e (Lam i ity x t' t, _) ty = do
  (a, tyA, (etyB,tyB)) <- Env.normalizePi e (Ident ity)
  let (e', tyB') = Env.instanciate e a (etyB,tyB) x
  let e'Withx = Env.addContext e' x (Ident tyA)
  t_n <- check e'Withx t' (Ident tyB')
  let eWithi = Env.addBinding e i (Env.Lam x t_n) (Ident ity)
  check eWithi t ty

-- let i : S = (x,y) in <t>
check e (Pair i ity x y t, _) ty = error "check pair"

-- let i : T = 'tagᵢ in <t>
check e (Tag i ity tag t, _) ty = do
  xfin <- Env.normalizeFin e (Ident ity)
  () <- if elem tag xfin then return ()
      else throw $ Check i (Ident ity) "Tag not included in Fin."
  let e_i = Env.addBinding e i (Env.ITag tag) (Ident ity)
  check e_i t ty


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

    (Env.Fin l1, Env.Fin l2) ->
         if unifyFin l1 l2 then return ()
         else throw $ Unification (Ident i) (Ident i')

    (_,_) -> throw $ Unification (Ident i) (Ident i')

unifyFin :: [String] -> [String] -> Bool
unifyFin l1 l2 =
    List.elem l1 $ List.permutations l2 -- We can do better
