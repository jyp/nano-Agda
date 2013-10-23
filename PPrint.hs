module PPrint where

import Names
import Terms
import qualified Data.Map as Map

import Text.PrettyPrint
import Numeric (showIntAtBase)

dot :: Doc
dot = char '.'

lambda :: Doc
lambda = char 'λ'

star :: Doc
star = char '★'

cross :: Doc
cross = char '×'

dcolons :: Doc
dcolons = text "::"

arrow :: Doc
arrow = char '→'

(<&>) :: Doc -> Doc -> Doc
d1 <&> d2 | isEmpty d2 = d1
d1 <&> d2 = d1 <+> text "and" <+> d2

infixl 8 <&>

scriptPretty :: String -> Int -> Doc
scriptPretty s = text . scriptShow s

scriptShow :: (Integral a, Show a) => [Char] -> a -> [Char]
scriptShow [] _ = []
scriptShow (minus:digits) x =
    if x < 0 then minus : sho (negate x) else sho x
    where sho y = showIntAtBase 10 (\i -> digits !! i) y []

subscriptPretty :: Int -> Doc
subscriptPretty = scriptPretty "-₀₁₂₃₄₅₆₇₈₉"

intro :: Doc
intro = char 'ᵢ'

elim :: Doc
elim = char 'ₑ'

-- Some pretty typeclass

class Pretty a where
    pretty :: a -> Doc

instance Pretty Doc where
    pretty = id

instance Pretty Int where
    pretty = int


-- default indentation
indentation :: Int
indentation = 2

-- Usefull hang operator
($+>) :: Doc -> Doc -> Doc
d $+> d' = hang d indentation d'

infixl 9 $+>

-- | Pretty positions

instance Pretty Position where
    pretty (Point l c) = int l <> colon <> int c
    pretty (Range l1 c1 l2 c2) | l1 == l2 =
        int l1 <> colon <> int c1 <> dot <> int c2
    pretty (Range l1 c1 l2 c2) =
        int l1 <> dot <> int l2 <> colon <>
        int c1 <> dot <> int c2

-- | Pretty identifier
ident :: Ident -> Doc
ident (i,n,_) = text n <> subscriptPretty i

instance Pretty Ident where
    pretty i = ident i

-- x:A
vartype :: Ident -> Ident -> Doc
vartype x tyA = ident x <+> colon <+> ident tyA

sort :: Int -> Doc
sort s = star <> subscriptPretty s

-- (x:A)×B
sigmaP :: Ident -> Ident -> Doc -> Doc
sigmaP x tyA tyB = parens (vartype x tyA) <+> cross <+> tyB

-- (x:A)→B
piP :: Ident -> Ident -> Doc -> Doc
piP x tyA tyB = parens (vartype x tyA) <+> arrow <+> tyB

-- { 'tag₁ , ... 'tagₙ }
finP :: [String] -> Doc
finP l = braces $ sep $ punctuate comma $ map text l

-- (x,y)
pairP :: Ident -> Ident -> Doc
pairP x y = parens $ ident x <> comma <+> ident y

-- λ(x:A).t
lamP :: Ident -> Doc -> Doc
lamP x t =
    (lambda <> ident x <> dot) $+> t

-- case x do { 'tagᵢ → tᵢ | i = 1..n }
caseP :: Ident -> [(String, Term)] -> Doc
caseP x l =
    text "case" <+> ident x <+> text "{" $+$
    (sep $ map f l) $$ text "}"
    where
      f (s,t) = (text s <+> arrow) $+> term t


-- let i = d in t
letP :: Doc -> Doc -> Doc -> Doc
letP i d t =
    sep [text "let" <+> i <+> equals , d , text "in" ] $+$
    t

letP1 :: Ident -> Doc -> Doc -> Doc
letP1 i = letP (ident i)

letP2 :: Ident -> Ident -> Doc -> Doc -> Doc
letP2 i1 i2 = letP $ pairP i1 i2

term :: Term -> Doc
term (t,_) =
    case t of
      Var i -> ident i

      Pi i s x tyA tyB t' ->
          letP (vartype i s) (piP x tyA $ term tyB) (term t')
      Lam i ty x tfun t' ->
          letP (vartype i ty) (lamP x $ term tfun) (term t')
      App i f x t' ->
          letP1 i (ident f <+> ident x) (term t')

      Sigma i s x tyA tyB t' ->
          letP (vartype i s) (sigmaP x tyA $ term tyB) (term t')
      Pair i ty x y t' ->
          letP (vartype i ty) (pairP x y) (term t')
      Proj i1 i2 z t' ->
          letP2 i1 i2 (ident z) (term t')

      Fin i s l t' ->
          letP (vartype i s) (finP l) (term t')
      Tag i ty s t' -> letP (vartype i ty) (text s) (term t')
      Case x l -> caseP x l
      Star i s t' -> letP1 i (sort s) (term t')

instance Pretty Term where
    pretty t = term t

-- | Pretty Statements

instance Pretty (Ident,Term,Term) where
    pretty (i,t,ty) =
        (ident i <+> dcolons) $+> term ty $+$
        (ident i <+> equals) $+> term t

instance Pretty [(Ident,Term,Term)] where
    pretty l = vcat $ map pretty l

instance Pretty Type where
    pretty (Sort s) = sort s
    pretty (Ident i) = pretty i

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
    pretty m =
        let l = Map.assocs m
            ld = map (\(k,v) -> pretty k <> colon <> pretty v) l
        in fsep $ punctuate comma ld
