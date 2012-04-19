{-# LANGUAGE GADTs, KindSignatures, OverloadedStrings, TypeSynonymInstances, RankNTypes, PatternGuards #-}
module Normal where

import Prelude hiding (length,elem,foldl,all,concatMap,and,drop,concat)
import Basics
import Display
import Data.Foldable
import Control.Arrow (first, second)
import Data.Sequence hiding (zip,replicate,reverse)
import Options

type NF = Term
type Neutral = Term

data Term :: * where
     Star :: Position -> Sort -> NF
     
     Pi  :: Ident -> NF -> NF -> NF
     Lam :: Ident -> NF -> NF -> NF 
     App :: Neutral -> NF -> Neutral
     
     Sigma  :: Position -> [(String,NF)] -> NF 
     Pair   :: Position -> [(String,NF)] -> NF -- Note: Unlike Sigma, Pair do not bind variables
     Proj   :: Neutral -> String -> Neutral      
              
     Fin :: [String] -> NF
     Tag :: String -> NF
     Cas :: [(String, NF)] -> NF

     V :: Position -> Int ->  -- ^ deBruijn index 
          Neutral
     Hole :: Position -> String -> Neutral
     
     Box :: Ident -> NF -> Term -> Subst -> NF
     -- | type annotation     
     Ann :: Neutral -> NF -> NF 
  deriving (Show)

termPosition t = case t of
   (Hole p _) -> p
   (Star p _) -> p
   (V p _) -> p
   (Pi i _ _) -> identPosition i
   (Sigma p _) -> p
   (Lam i _ _) -> identPosition i
   (Pair p _ ) -> p
   (App x y) -> s x
   (Proj x _) -> s x
   (Ann x _) -> s x 
   _ -> dummyPosition
  where s = termPosition

type Subst = [NF]

var = V dummyPosition
hole = Hole dummyPosition
star = Star dummyPosition
sigma = Sigma dummyPosition
pair = Pair dummyPosition
tag = Tag
fin = Fin
cas = Cas

identity = map var [0..]

subst0 :: NF -> Subst
subst0 u = u:identity

-- | Weakening
wkn :: Int -> Subst
wkn n = map var [n..]

wk = wkn 1

-- | Hereditary substitution application
apply :: Subst -> Term -> NF
apply f t = case t of
  Star p x -> Star p x
  Lam i ty bo -> Lam i (s ty) (s' bo)
  Pair i fs -> Pair i (map (second s) fs)
  Pi i a b -> Pi i (s a) (s' b)
  Sigma i [] -> Sigma i []
  Sigma i ((f,x):xs) -> let Sigma _ xs' = s' (sigma xs) in Sigma i ((f,s x):xs')
  (App a b) -> app (s a) (s b)
  (Proj x k) -> proj (s x) k 
  Hole p x -> Hole p x
  V _ x -> f !! x
  Box n t e g -> Box n (s t) (s' e) (map s g)
  Ann x t -> ann (s x) (s t)
  
  Cas cs -> cas (map (second s) cs)
  Fin x -> Fin x
  Tag x -> Tag x
 where s' = apply (var 0 : wk ∘ f)
       s  = apply f

(∙) = apply
σ ∘ ρ = map (apply σ) ρ

ann x t = Ann x t

-- | Hereditary application
app :: NF -> NF -> NF 
app (Lam i _ bo) u = subst0 u ∙ bo
app (Cas cs)     (Tag t) | Just x <- lookup t cs = x
app n            u = App n u

-- | Hereditary projection
proj :: NF -> String -> NF
proj (Pair _ fs) f | Just x <- lookup f fs = x
proj x k = Proj x k 

-----------------------------------
-- Display

dec xs = [ x - 1 | x <- xs, x > 0]

freeVars :: Term -> [Int]
freeVars (Pi _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (Sigma _ []) = []
freeVars (Sigma _ ((_,x):xs)) = freeVars x <> (dec $ freeVars (sigma xs))
freeVars (V _ x) = [x]
freeVars (App a b) = freeVars a <> freeVars b
freeVars (Lam _ ty b) = freeVars ty <> (dec $ freeVars b)
freeVars (Star _ _) = mempty
freeVars (Hole _ _) = mempty
freeVars (Pair _ xs) = concatMap (freeVars . snd) xs
freeVars (Proj x _) = freeVars x
freeVars (Box _ t e env) = freeVars t <> concat [freeVars (env!!x) | x <- dec (freeVars e)]
freeVars (Ann x t) = freeVars x <> freeVars t
freeVars (Fin _) = []
freeVars (Tag _) = []
freeVars (Cas cs) = concatMap (freeVars . snd) cs

iOccursIn :: Int -> Term -> Bool
iOccursIn x t = x `elem` (freeVars t)

allocName :: DisplayContext -> Ident -> Ident
allocName g s 
  | s `elem` g = allocName g (modId (++ "'") s)
  | otherwise = s

cPrint :: Int -> DisplayContext -> Term -> Doc
cPrint p ii (Hole _ x) = text x
cPrint p ii (Star _ i) = pretty i
cPrint p ii (V _ k) 
  | k < 0 || k >= length ii  = text "<global " <+> pretty (k - length ii) <> ">"
  | otherwise = pretty (ii `index` k) 
cPrint p ii (Proj x f)      = cPrint p ii x <> "." <> text f 
cPrint p ii t@(App _ _)     = let (fct,args) = nestedApp t in 
                                 parensIf (p > 3) (cPrint 3 ii fct <+> sep [ cPrint 4 ii a | a <- args]) 
cPrint p ii t@(Pi _ _ _)    = parensIf (p > 1) (printBinders "→" ii mempty $ nestedPis t)
cPrint p ii t@(Sigma _ _) = parensIf (p > 1) (printBinders "×" ii mempty $ nestedSigmas t)
cPrint p ii (t@(Lam _ _ _)) = parensIf (p > 1) (nestedLams ii mempty t)
cPrint p ii (Pair _ fs) = parensIf (p > (-1)) (sep (punctuate comma [text name <+> text "=" <+> cPrint 0 ii x | (name,x) <- fs ]))
cPrint p ii (Box x t e env) = "<" <> pretty i <> nv 
--                              <> ":" <> cPrint 0 ii t
                              <> ">"
        where i = allocName ii x
              nv = "[" <> sep (punctuate ";" (dispEnv ii [(f,env!!f) | f <- dec (freeVars t)])) <> "]"
cPrint p ii (Ann x t) = parensIf (p > 0) (cPrint 0 ii x <+> ":" <+> cPrint 0 ii t)
cPrint p ii (Fin ts) = "[" <> sep (punctuate comma (map text ts)) <> "]"
cPrint p ii (Tag t) = "'" <> text t
cPrint p ii (Cas cs) = "case {" <> sep (punctuate ";" [text c <> "↦" <> cPrint 0 ii a | (c,a) <- cs]) <> "}"

-- FIXME: should remember the variable names in the substitution
dispEnv :: DisplayContext -> [(Int,NF)] -> [Doc]
dispEnv ii g = [pretty i <> "↦" <> cPrint 0 ii v | (i,v) <- g]

nestedPis  :: NF -> ([(Ident,Bool,NF)], NF)
nestedPis (Pi i a b) = (first ([(i,0 `iOccursIn` b,a)] ++)) (nestedPis b)
nestedPis x = ([],x)

nestedSigmas  :: NF -> ([(Ident,Bool,NF)], NF)
nestedSigmas (Sigma _ ((i,x):xs)) = (first ([(synthId i,0 `iOccursIn` sigma xs,x)] ++)) (nestedSigmas (sigma xs))
nestedSigmas (Sigma _ []) = ([],hole "⊤")

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


