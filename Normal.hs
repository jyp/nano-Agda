{-# LANGUAGE GADTs, KindSignatures, OverloadedStrings, TypeSynonymInstances, TypeFamilies, MultiParamTypeClasses, RankNTypes #-}
module Normal where

import Prelude hiding (length,elem,foldl)
import Basics
import Display
import Data.Foldable
import Control.Arrow (first, second)
import Data.Sequence hiding (zip,replicate,reverse)
import Options

type NF = Term
type Neutral = Term

data Term :: * where
     Star :: Sort -> NF
     
     Pi  :: Ident -> NF -> NF -> NF
     Lam :: Ident -> NF -> NF -> NF 
     App :: Neutral -> NF -> Neutral
     
     Sigma :: Ident -> NF -> NF -> NF
     Pair  :: Ident -> NF -> NF -> NF  -- Pair does not bind any variable.
     Proj  :: Neutral -> Bool -> -- ^ True for 1st projection; False for 2nd.
              Irr String -> Neutral 
     
     V :: Int ->  -- ^ deBruijn index 
          Neutral
     Hole :: String -> Neutral
  deriving (Eq, Show)

type Subst = [NF]

var = V

-- | Hereditary substitution
subst0 :: NF -> NF -> NF
subst0 u = subst (u:map (var) [0..])  

subst :: Subst -> Term -> NF
subst f t = case t of
  Star x -> Star x
  Lam i ty bo -> Lam i (s ty) (s' bo)
  Pair i x y -> Pair i (s x) (s y)
  Pi i a b -> Pi i (s a) (s' b)
  Sigma i a b -> Sigma i (s a) (s' b)
  (App a b) -> app (s a) (s b)
  (Proj x k f) -> proj (s x) k f
  Hole x -> hole x
  V x -> f !! x
 where s,s' :: forall n. Term -> NF
       s' = subst (var 0 : map wk f)
       s  = subst f


-- | Hereditary application
app :: NF -> NF -> NF 
app (Lam i _ bo) u = subst0 u bo
app n            u = App n u

-- | Hereditary projection
proj :: NF -> Bool -> Irr String -> NF
proj (Pair _ x y) True f = x
proj (Pair _ x y) False f = y
proj x k f = Proj x k f

hole = Hole

-- | Weakening
wkn :: Int -> NF -> NF
wkn n = subst (map var [n..])

wk = wkn 1

-- | Inverse of weakening
str = subst0 (hole "str: oops!")

-----------------------------------
-- Display

dec xs = [ x - 1 | x <- xs, x > 0]

freeVars :: Term -> [Int]
freeVars (Pi _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (Sigma _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (V x) = [x]
freeVars (App a b) = freeVars a <> freeVars b
freeVars (Lam _ ty b) = freeVars ty <> (dec $ freeVars b)
freeVars (Star _) = mempty
freeVars (Hole _) = mempty
freeVars (Pair _ x y) = freeVars x <> freeVars y
freeVars (Proj x _ _) = freeVars x

iOccursIn :: Int -> Term -> Bool
iOccursIn x t = x `elem` (freeVars t)

allocName :: DisplayContext -> Ident -> Ident
allocName g s 
  | fromIrr s `elem` (fmap fromIrr g) = allocName g (modId (++ "'") s)
  | otherwise = s

cPrint :: Int -> DisplayContext -> Term -> Doc
cPrint p ii (Hole x) = text x
cPrint p ii (Star i) = pretty i
cPrint p ii (V k) 
  | k < 0 || k >= length ii  = text "<deBrujn index" <+> pretty k <+> text "out of range>"
  | otherwise = pretty (ii `index` k) 
cPrint p ii (Proj x k (Irr f))     = cPrint p ii x <> (if k then "." <> text f else "/")
cPrint p ii t@(App _ _)     = let (fct,args) = nestedApp t in 
                                 parensIf (p > 3) (cPrint 3 ii fct <+> sep [ cPrint 4 ii a | a <- args]) 
cPrint p ii t@(Pi _ _ _)    = parensIf (p > 1) (printBinders "→" ii mempty $ nestedPis t)
cPrint p ii t@(Sigma _ _ _) = parensIf (p > 1) (printBinders "×" ii mempty $ nestedSigmas t)
cPrint p ii (t@(Lam _ _ _)) = parensIf (p > 1) (nestedLams ii mempty t)
cPrint p ii (Pair name x y) = parensIf (p > (-1)) (sep [pretty name <+> text "=" <+> cPrint 0 ii x <> comma,
                                                          cPrint (-1) ii y])

nestedPis  :: NF -> ([(Ident,Bool,NF)], NF)
nestedPis (Pi i a b) = (first ([(i,0 `iOccursIn` b,a)] ++)) (nestedPis b)
nestedPis x = ([],x)

nestedSigmas  :: NF -> ([(Ident,Bool,NF)], NF)
nestedSigmas (Sigma i a b) = (first ([(i,0 `iOccursIn` b,a)] ++)) (nestedSigmas b)
nestedSigmas x = ([],x)

printBinders :: Doc -> DisplayContext -> Seq Doc -> ([(Ident,Bool,NF)], NF) -> Doc
printBinders sep ii xs (((x,occurs,a):pis),b) = printBinders sep (i <| ii) (xs |> (printBind' ii i occurs a <+> sep)) (pis,b)
        where i = allocName ii x
printBinders _ ii xs ([],b)                 = sep $ toList $ (xs |> cPrint 1 ii b) 


nestedLams :: DisplayContext -> Seq Doc -> Term -> Doc
nestedLams ii xs (Lam x ty c) = nestedLams (i <| ii) (xs |> parens (pretty i <+> ":" <+> cPrint 0 ii ty)) c
                                  where i = allocName ii x
nestedLams ii xs t         = (text "\\ " <> (sep $ toList $ (xs |> "->")) <+> nest 3 (cPrint 0 ii t))

printBind' ii name occurs d = case not (isDummyId name) || occurs of
                  True -> parens (pretty name <+> ":" <+> cPrint 0 ii d)
                  False -> cPrint 2 ii d
                  
nestedApp :: Neutral -> (Neutral,[NF])
nestedApp (App f a) = (second (++ [a])) (nestedApp f)
nestedApp t = (t,[])

prettyTerm = cPrint (-100)


instance Pretty Term where
    pretty = prettyTerm mempty


