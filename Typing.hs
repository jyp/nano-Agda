module Typing where

import Common
import Names
import Terms
import Env(Env)
import qualified Env as Env


checkDec :: (Ident,Term,Type) -> TypeError (Env,Term,Type)
checkDec = undefined

checkSort :: Env -> Ident -> Sort -> TypeError ()
checkSort e i s =
    let is = Env.getSort e i in
    if is < s then return ()
    else throw (CheckI i (Star s,dummyPos))

-- | Type checking

check :: Env -> Term -> Type -> TypeError (Env,Term)

-- Vars
check e t@(Var i, _) ty = do
    () <- unify e (Env.getType e i) ty
    return (e, t)

-- *ᵢ
-- TODO : Not sure if it's possible to have something else as type.
check e t@(Star s, _) ty@(Star s', _) =
    if s < s' then return (e, t)
    else throw $ CheckT t ty

-- | Types

-- Π
check e (Pi i s x tyA tyB t , pos) ty =
    let ttyA = (Var tyA, pos)
        star = (Star s, pos)
    in do
    () <- checkSort e tyA s
    eWithx <- Env.addContext e x ttyA
    _ <- check eWithx tyB (below star)
    eWithi <- Env.typePi e i star x tyA tyB
    check eWithi t ty

-- Σ
check e (Sigma i s x tyA tyB t , pos) ty =
    let ttyA = (Var tyA, pos)
        star = (Star s, pos)
    in do
    () <- checkSort e tyA s
    eWithx <- Env.addContext e x ttyA
    _ <- check eWithx tyB (below star)
    eWithi <- Env.typeSigma e i star x tyA tyB
    check eWithi t ty

-- Fin
check e (Fin i l t , pos) ty =
    let star = (Star 1, pos) in do
    eWithi <- Env.typeFin e i star l
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

unify :: Env -> Term -> Term -> TypeError ()
unify e t t' = undefined
