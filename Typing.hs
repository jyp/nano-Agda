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


check :: Env -> Term -> Type -> TypeError (Env,Term)

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

-- let i : T = (x,y) in t : C
check e (Pair i tT x y t , pos) ty =
    undefined
