module Env where

import Common

import Names
import PPrint
import Text.PrettyPrint(($$),($+$),(<>),(<+>),text)
import qualified Text.PrettyPrint as P
import qualified Terms as T
import Data.Maybe(fromMaybe)
import Data.List(find)

import qualified Data.Map as M

data Definition
    = Appl Ident Ident          -- y = f x
    | Lam Ident (Env,Ident)     -- f = λx.t
    | ITag String               -- x = 'tag
    | ETag String               -- x = 'tag
    | IPair Ident Ident         -- z = (x,y)
    | EPair Ident Ident         -- (x,y) = z
    | Alias Ident               -- z = z'
    | Pi Ident Ident (Env,Ident)     -- σ = (x:A)→B
    | Sigma Ident Ident (Env,Ident)  -- σ = (x:A)×B
    | Fin [String]              -- σ = { 'bla, 'bli, 'blo }
    | Star Int                  -- σ = *ᵢ
    deriving (Eq)

instance Pretty Definition where
    pretty (Appl f x) = pretty f <+> pretty x
    pretty (Lam i t) = lamP i (pretty t)
    pretty (ITag x) = text x <> intro
    pretty (ETag x) = text x <> elim
    pretty (IPair x y) = pairP x y <> intro
    pretty (EPair x y) = pairP x y <> elim
    pretty (Alias x) = pretty x
    pretty (Pi x tyA tyB) = piP x tyA $ pretty tyB
    pretty (Sigma x tyA tyB) = sigmaP x tyA $ pretty tyB
    pretty (Fin l) = finP l
    pretty (Star i) = sort i

type Context = M.Map Name T.Type
type EnvIntro = M.Map Name Definition
type EnvElim = M.Map Name [Definition]

data Env = Env Context EnvIntro EnvElim
    deriving (Eq)

(∪) :: Env -> Env -> Env
(Env c1 ei1 ee1) ∪ (Env c2 ei2 ee2) =
    let c = M.union c1 c2
        ei = M.union ei1 ei2
        ee = M.unionWith (++) ee1 ee2
    in Env c ei ee

instance Pretty Env where
    pretty (Env c ei _) =
        P.text "Context :" <+> pretty c $+$
        P.text "EnvIntro :" <+> pretty ei

instance Pretty (Env,Ident) where
    pretty (_,i) = P.text "<stuff," <+> pretty i <+> P.text ">"

instance Pretty (Env, [(Ident, Ident, Ident)]) where
    pretty (e,l) =
        pretty e $+$ (P.vcat $ map printdef l)
            where
              printdef (i,t,ty) =
                  pretty i
                  <+> P.colon <+> pretty ty
                  <+> P.equals <+> pretty t

mapName :: (Name -> Name) -> Env -> Env
mapName f (Env c ei ee) =
    let mapT f (T.Sort s) = T.Sort s
        mapT f (T.Ident i) = T.Ident $ f i
        c'  = M.map (mapT (>~ f)) $ M.mapKeys f c
        ei' = M.map (mapNameDef f) $ M.mapKeys f ei
        ee' = M.map (map $ mapNameDef f) $ M.mapKeys f ee
    in Env c' ei' ee'

mapNameDef :: (Name -> Name) -> Definition -> Definition
mapNameDef map def =
    let m = (>~ map) in
    case def of
      Appl f x -> Appl (m f) (m x)
      Lam i (e,x) -> Lam (m i) (mapName map e, m x)
      ITag x -> ITag x
      ETag x -> ETag x
      IPair x y -> IPair (m x) (m y)
      EPair x y -> EPair (m x) (m y)
      Alias x -> Alias $ m x
      Pi x tyA (e,tyB) -> Pi (m x) (m tyA) $ (mapName map e, m tyB)
      Sigma x tyA (e,tyB) -> Sigma (m x) (m tyA) $ (mapName map e, m tyB)
      Fin l -> Fin l
      Star i -> Star i


empty :: Env
empty = Env M.empty M.empty M.empty

getType :: Env -> Ident -> TypeError T.Type
getType (Env c _ _) ident@(i,_,_) =
    case M.lookup i c of
      Just t -> return t
      Nothing ->
          throw . UnknownError $
          text "Variable" <+> pretty ident <+>
          text "doesn't have a type."

getIntro :: Env -> Ident -> TypeError Definition
getIntro (Env _ e _) ident@(i,_,_) =
    case M.lookup i e of
      Just t -> return t
      Nothing ->
          throw . UnknownError $
          text "Variable" <+> pretty ident <+>
          text "doesn't have an introduction."

getElims :: Env -> Ident -> TypeError [Definition]
getElims (Env _ _ e) ident@(i,_,_) =
    case M.lookup i e of
      Just t -> return t
      Nothing ->
          throw . UnknownError $
          text "Variable" <+> pretty ident <+>
          text "doesn't have any elimination."

getVal :: Env -> Ident -> Either Definition [Definition]
getVal e@(Env _ ei ee) (i,_,_) =
    case M.lookup i ei of
      Just (Alias x) -> getVal e x
      Just x -> Left x
      Nothing -> Right $ ee M.! i

addContext :: Env -> Ident -> T.Type -> Env
addContext (Env context ei ee) id@(i,_,_) ty =
    let context' = M.insert i ty context
    in Env context' ei ee

addIntro :: Env -> Ident -> Definition -> Env
addIntro (Env context ei ee) id@(i,_,_) t =
  let ei' = M.insert i t ei
  in Env context ei' ee

addBinding :: Env -> Ident -> Definition -> T.Type -> Env
addBinding env id t ty =
  let env' = addContext env id ty in
  addIntro env' id t

addElim :: Env -> Ident -> Definition -> Env
addElim (Env context ei ee) id@(i,_,_) t =
  let elims = fromMaybe [] $ M.lookup i ee
      ee' = M.insert i (t:elims) ee
  in Env context ei ee'

addAlias :: Env -> Ident -> Ident -> TypeError Env
addAlias env x y = do
  ty <- getType env y
  return $ addBinding env x (Alias y) ty

-- This function is used to "instanciate" a lambda form :
-- with the env e, the lambda expression in normal form lam = (x, e', f) applied to x
-- instanciate e x y lam = (e ++ e'[x:=y], f)
instanciate :: Env -> Ident -> (Env, Ident) -> Ident -> (Env,Ident)
instanciate e (x,_,_) (et , f) (y,_,_) =
    let replace a = if a == x then y else x
        et' = mapName replace et
        f' = f >~ replace
    in (e ∪ et', f)

-- | Verification functions

(!) :: Env -> Ident -> TypeError Definition
env@(Env _ e _) ! id@(i,_,_) =
    case M.lookup i e of
      Just (Alias x) -> env ! x
      Just d -> return d
      Nothing -> throw $ Abstract id

infix 9 !

-- Check if i == i', modulo Aliases
areEqual :: Env -> Ident -> Ident -> Bool
areEqual env@(Env _ e _) id@(i,_,_) id'@(i',_,_) =
    i == i' ||
    case (M.lookup i e , M.lookup i' e) of
      (Just (Alias a), Nothing) -> areEqual env a id'
      (Nothing, Just (Alias a')) -> areEqual env id a'
      (Just (Alias a), Just (Alias a')) -> areEqual env a a'
      (_ , _) -> False

normalizeSort :: Env -> Ident -> TypeError T.Sort
normalizeSort env i = do
  def <- env ! i
  case def of
    Star s -> return s
    _ -> throw $ Abstract i

normalizeSort' :: Env -> T.Type -> TypeError T.Sort
normalizeSort' e ty =
    case ty of
      T.Sort s -> return s
      T.Ident i -> normalizeSort e i

normalizePi :: Env -> Ident -> TypeError (Ident, Ident, (Env,Ident))
normalizePi env i = do
  def <- env ! i
  case def of
    Pi x tyA tyB -> return (x,tyA,tyB)
    _ -> throw $ Normalize (T.Ident i) "Expected Pi."

normalizeSigma :: Env -> Ident -> TypeError (Ident, Ident, (Env,Ident))
normalizeSigma env i = do
  def <- env ! i
  case def of
    Sigma x tyA tyB -> return (x,tyA,tyB)
    _ -> throw $ Normalize (T.Ident i) "Expected Sigma."

normalizeFin :: Env -> T.Type -> TypeError [String]
normalizeFin env ty =
  case ty of
    T.Sort _ ->
        throw $ Normalize ty "Expected Fin, got Sort."
    T.Ident i -> do
        def <- env ! i
        case def of
          Fin l -> return l
          _ -> throw $ Normalize ty "Expected Fin."

-- Verify that the definition of a variable has well formed tag intro and elim.
checkTag :: Env -> Ident -> Bool
checkTag e@(Env _ ei ee) id@(i,_,_)  =
    let intro = M.lookup i ei in
    case intro of
      Just (Alias i') -> checkTag e i'
      Just (ITag s) ->
          let elim = fromMaybe [] $ M.lookup i ee
              x = find f elim
              f (ETag _) = True
              f _ = False
          in case x of
               Just (ETag s') | s /= s' -> False
               _ -> True
      _ -> True

elimTag :: Env -> Ident -> String -> Env
elimTag env i s =
  addIntro env i (ETag s)
