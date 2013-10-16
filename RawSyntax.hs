module RawSyntax where

import Common
import qualified Terms as T
import qualified Names as N

import Data.List(sortBy,groupBy)
import Data.Ord(comparing)
import qualified Data.Map as Map

-- | The abstract syntax tree.

type Position = (Int,Int,Int)

pointPos :: Position -> N.Position
pointPos (_,l,c) = N.Point l c

rangePos :: Position -> Position -> N.Position
rangePos (_,l1,c1) (_,l2,c2) = N.Range l1 c1 l2 c2

newtype Tag = TTag (Position,String) deriving (Eq,Ord,Show)
newtype Ident = Ident (Position,String) deriving (Eq,Ord,Show)

data Smt =
   TypDec Ident Term
 | Def Ident Term
  deriving (Eq,Ord,Show)

type VarType = (Ident, Ident)

type Pair = (Ident, Ident)

data Term =
   Var   Ident
 | Pi    Position Ident Ident VarType Term Position Term
 | Lam   Position Ident Ident Ident Term   Position Term
 | App   Position Ident Ident Ident        Position Term
 | Sigma Position Ident Ident VarType Term Position Term
 | Pair  Position Ident Ident Pair         Position Term
 | Proj  Position Pair Ident               Position Term
 | Fin   Position Ident Ident [Tag]        Position Term
 | Tag   Position Ident Ident Tag          Position Term
 | Case  Position Ident [CaseCont]
 | Star  Position Ident Int                Position Term
  deriving (Eq,Ord,Show)

data CaseCont = CaseCont Tag Term
  deriving (Eq,Ord,Show)

-- | Main translation function

getIdent :: N.NameEnv -> Ident -> N.Ident
getIdent e (Ident (p,i)) = N.getIdent e (i,pointPos p)

freshIdent :: N.NameEnv -> Ident -> N.FreshM (N.NameEnv, N.Ident)
freshIdent e (Ident (p,i)) = do
  (m, i') <- N.freshIdent e (i,pointPos p)
  return ( m, i')

getPos :: Term -> N.Position
getPos t =
    case t of
      Var (Ident (p,_)) -> pointPos p
      Pi p _ _ _ _ p' _ -> rangePos p p'
      Lam p _ _ _ _ p' _ -> rangePos p p'
      App p _ _ _ p' _ -> rangePos p p'
      Sigma p _ _ _ _ p' _ -> rangePos p p'
      Pair p _ _ _ p' _ -> rangePos p p'
      Proj p _ _ p' _ -> rangePos p p'
      Fin p _ _ _ p' _ -> rangePos p p'
      Tag p _ _ _ p' _ -> rangePos p p'
      Case p _ _ -> pointPos p
      Star p _ _ p' _ -> rangePos p p'

toTerm' :: N.NameEnv -> Term -> N.FreshM T.Term'
toTerm' e term =
    case term of
      Var i ->
          return $ T.Var (getIdent e i)
      Pi _ i s (x,tyA) tyB _ t -> do
          (e_i,i') <- freshIdent e i
          let tyA' = getIdent e tyA
          let s' = getIdent e s
          (e_x,x') <- freshIdent e x
          tyB' <- toTerm e_x tyB
          t' <- toTerm e_i t
          return $ T.Pi i' s' x' tyA' tyB' t'
      Lam _ i ty x tx _ t -> do
          (e_i,i') <- freshIdent e i
          let ty' = getIdent e ty
          (e_x,x') <- freshIdent e x
          tx' <- toTerm e_x tx
          t' <- toTerm e_i t
          return $ T.Lam i' ty' x' tx' t'
      App _ i f x _ t -> do
          (e_i,i') <- freshIdent e i
          let f' = getIdent e f
          let x' = getIdent e x
          t' <- toTerm e_i t
          return $ T.App i' f' x' t'
      Sigma _ i s (x,tyA) tyB _ t -> do
          let tyA' = getIdent e tyA
          let s' = getIdent e s
          (e_i,i') <- freshIdent e i
          (e_x,x') <- freshIdent e x
          tyB' <- toTerm e_x tyB
          t' <- toTerm e_i t
          return $ T.Sigma i' s' x' tyA' tyB' t'
      Pair _ i ty (x,y) _ t -> do
          let ty' = getIdent e ty
          (e_i,i') <- freshIdent e i
          let x' = getIdent e x
          let y' = getIdent e y
          t' <- toTerm e_i t
          return $ T.Pair i' ty' x' y' t'
      Proj _ (x,y) z _ t -> do
          let z' = getIdent e z
          (e_x,x') <- freshIdent e x
          (e_xy,y') <- freshIdent e_x y
          t' <- toTerm e_xy t
          return $ T.Proj x' y' z' t'
      Fin _ i s l _ t -> do
          (e_i,i') <- freshIdent e i
          let s' = getIdent e s
          let l' = map (\ (TTag (_,tag)) -> tag) l
          t' <- toTerm e_i t
          return $ T.Fin i' s' l' t'
      Tag _ i ty (TTag (_,tag))  _ t -> do
          (e_i,i') <- freshIdent e i
          let ty' = getIdent e ty
          t' <- toTerm e_i t
          return $ T.Tag i' ty' tag t'
      Case _ i l -> do
          (e_i,i') <- freshIdent e i
          let toCases (CaseCont (TTag (_,tag)) t) =
                  do { t' <- toTerm e_i t ; return (tag,t') }
          cases <- mapM toCases l
          return $ T.Case i' cases
      Star _ i s _ t -> do
          (e_i,i') <- freshIdent e i
          t' <- toTerm e_i t
          return $ T.Star i' s t'

toTerm :: N.NameEnv -> Term -> N.FreshM T.Term
toTerm e t = do
  let pos = getPos t
  t' <- toTerm' e t
  return (t',pos)

-- | Utility translation functions

smtToTerm :: N.NameEnv -> (Ident,Term,Term) ->
            N.FreshM (N.NameEnv, (N.Ident, T.Term, T.Term))
smtToTerm e (i, t, ty) = do
    (e', i') <- freshIdent e i
    ty' <- toTerm e ty
    t' <- toTerm e t
    return (e', (i', t', ty'))

smtGetIdent :: Smt -> Ident
smtGetIdent (TypDec i _ ) = i
smtGetIdent (Def i _ ) = i

smtGetIdString :: Smt -> String
smtGetIdString = (\(Ident (_,i)) -> i) . smtGetIdent

groupSmt :: [Smt] -> Err [(Ident,Term,Term)]
groupSmt decs =
    let decsSort = Data.List.sortBy (comparing smtGetIdString) decs
        decsGroup = groupBy (\x y -> smtGetIdString x == smtGetIdString y) decsSort
    in mapM f decsGroup where
        f [ TypDec i ty , Def _ t ] = return (i,t,ty)
        f [ Def i t , TypDec _ ty ] = return (i,t,ty)
        f [ Def i _ ] =
            throw $ "Definition of " ++ show i ++ " lacks a type declaration."
        f [ TypDec i _ ] =
            throw $ "Type declaration of " ++ show i ++ " lacks a definition."
        f (h:_) =
            throw $ show (smtGetIdent h) ++ " has multiple definitions or declarations."
        f [] = error "empty group int statements."



convertFile :: [Smt] -> Err [(N.Ident,T.Term,T.Term)]
convertFile l = do
  let e = Map.empty
  decs <- groupSmt l
  let (_, decs') = N.runFresh $ scanfoldl smtToTerm e decs
  return $ reverse $ decs'
