module PPrint (module Text.PrettyPrint, module PPrint) where

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

-- | Some pretty typeclass

class Pretty a where
    pretty :: a -> Doc

instance Pretty Doc where
    pretty = id

instance Pretty Int where
    pretty = int

-- Pretty operators

(<:>) :: (Pretty a, Pretty b) => a -> b -> Doc
d1 <:> d2 = pretty d1 <+> colon <+> pretty d2

infixl 8 <:>

(<.>) :: (Pretty a, Pretty b) => a -> b -> Doc
d1 <.> d2 = pretty d1 <+> dot <+> pretty d2

infixl 8 <.>

-- default indentation
indentation :: Int
indentation = 2

-- Usefull hang operator
($+>) :: Doc -> Doc -> Doc
d $+> d' = hang d indentation d'

infixl 9 $+>

-- x:A
vartype :: (Pretty a, Pretty b) => a -> b -> Doc
vartype x tyA = x <:> tyA

sort :: Int -> Doc
sort s = star <> subscriptPretty s

-- (x:A)×B
sigmaP :: (Pretty a, Pretty b) => a -> b -> Doc -> Doc
sigmaP x tyA tyB = parens (vartype x tyA) <+> cross <+> tyB

-- (x:A)→B
piP :: (Pretty a, Pretty b) => a -> b -> Doc -> Doc
piP x tyA tyB = parens (vartype x tyA) <+> arrow <+> tyB

-- { 'tag₁ , ... 'tagₙ }
finP :: [String] -> Doc
finP l = braces $ sep $ punctuate comma $ map text l

-- (x,y)
pairP :: (Pretty a, Pretty b) => a -> b -> Doc
pairP x y = parens $ pretty x <> comma <+> pretty y

-- λ(x:A).t
lamP :: Pretty a => a -> Doc -> Doc
lamP x t =
    (lambda <> pretty x <> dot) $+> t

-- case x do { 'tagᵢ → tᵢ | i = 1..n }
caseP :: Pretty a => a -> [(String, Doc)] -> Doc
caseP x l =
    text "case" <+> pretty x <+> text "{" $+$
    (sep $ map f l) $$ text "}"
    where
      f (s,t) = (text s <+> arrow) $+> t

-- let i = d in t
letP :: Doc -> Doc -> Doc -> Doc
letP i d t =
    sep [text "let" <+> i <+> equals , d , text "in" ] $+$
    t

letP1 :: Pretty a => a -> Doc -> Doc -> Doc
letP1 i = letP (pretty i)

letP2 :: (Pretty a, Pretty b) => a -> b -> Doc -> Doc -> Doc
letP2 i1 i2 = letP $ pairP i1 i2

-- | Pretty Stuff

showP :: Pretty a => a -> String
showP x = show (pretty x)

instance Pretty a => Pretty [a] where
    pretty l = vcat $ map pretty l

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
    pretty m =
        let l = Map.assocs m
            ld = map (\(k,v) -> pretty k <> colon <> pretty v) l
        in fsep $ punctuate comma ld
