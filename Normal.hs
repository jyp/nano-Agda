{-# LANGUAGE GADTs, KindSignatures, OverloadedStrings, TypeSynonymInstances, TypeFamilies, MultiParamTypeClasses, RankNTypes, PatternGuards #-}
module Normal where

import Prelude hiding (length,elem,foldl,all,concatMap,and,drop)
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
              
     V :: Position -> Int ->  -- ^ deBruijn index 
          Neutral
     Hole :: Position -> String -> Neutral
     
     Box :: Ident -> Term -> Subst -> NF
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
  where s = termPosition

instance Eq Term where
  Star _ s == Star _ s' = s == s'
  Pi _ a b == Pi _ a' b' = a == a' && b == b'
  Lam _ a b == Lam _ a' b' = a == a' && b == b'
  App a b == App a' b' = a == a' && b == b'
  Sigma _ xs == Sigma _ xs' = xs == xs'
  Pair _ xs == Pair _ xs' = xs == xs'
  Proj x f == Proj x' f' = x == x' && f == f'
  V _ x == V _ x' = x == x'
  Hole _ _ == Hole _ _ = True
  Box n t g == Box n' t' g' = n == n' && and [g!!v == g'!!v | v <- freeVars t]
  Ann x _ == Ann x' _ = x == x'
  _ == _ = False


-- | Untyped evaluation -- of boxes only.
evaluate box@(Box n e0 env) = return $ apply (box:wk ∘ env) e0
evaluate (Proj x f) = (\t -> proj t f) <$> evaluate x
evaluate (App f x) = (`app` x) <$> evaluate f 
evaluate _ = Nothing


type Subst = [NF]

var = V dummyPosition
hole = Hole dummyPosition
star = Star dummyPosition
sigma = Sigma dummyPosition
pair = Pair dummyPosition

identity = map var [0..]

subst0 :: NF -> Subst
subst0 u = u:identity

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
  Box p x g -> Box p x (map s g)
  Ann x t -> Ann (s x) (s t)
 where s' = apply (var 0 : wk ∘ f)
       s  = apply f

(∙) = apply
σ ∘ ρ = map (apply σ) ρ

-- | Hereditary application
app :: NF -> NF -> NF 
app (Lam i _ bo) u = subst0 u ∙ bo
app n            u = App n u

-- | Hereditary projection
proj :: NF -> String -> NF
proj (Pair _ fs) f | Just x <- lookup f fs = x
proj x k = Proj x k 

-- | Weakening
wkn :: Int -> Subst
wkn n = map var [n..]

wk = wkn 1

-- | Inverse of weakening
str = subst0 (hole "str: oops!")

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
freeVars (Box _ b _) = dec (freeVars b)
freeVars (Ann x t) = freeVars x <> freeVars t

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
cPrint p ii (Box i t g) = pretty i <> {- cPrint 100 (i <| ii) t <> -} "[" <> sep (punctuate ";" (dispEnv ii [(ii `index` f,g!!f) | f <- dec (freeVars t)])) <> "]" 
cPrint p ii (Ann x t) = parensIf (p > 0) (cPrint 0 ii x <+> ":" <+> cPrint 0 ii t)

dispEnv :: DisplayContext -> [(Ident,NF)] -> [Doc]
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


