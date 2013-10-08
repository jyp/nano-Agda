module PPrint where

import Names
import Terms

import Text.PrettyPrint
import Numeric (showIntAtBase)

-- default indentation
indentation :: Int
indentation = 2

ident :: Ident -> Doc
ident (i,n,_) = text n <> int i

-- x:A
vartype :: Ident -> Ident -> Doc
vartype x tyA = ident x <> colon <> ident tyA

-- x:*ᵢ
varsort :: Ident -> Int -> Doc
varsort x s = ident x <> colon <> sort s

-- (x:A)×B
sigmaP :: Ident -> Ident -> Term -> Doc
sigmaP x tyA tyB = parens (vartype x tyA) <> text "×" <> term tyB

-- (x:A)→B
piP :: Ident -> Ident -> Term -> Doc
piP x tyA tyB = parens (vartype x tyA) <> text "→" <> term tyB

-- { 'tag₁ , ... 'tagₙ }
finP :: [String] -> Doc
finP l = sep $ punctuate (char ',') $ map text l

-- (x,y)
pairP :: Ident -> Ident -> Doc
pairP x y = parens (ident x <> text ", " <> ident y)

-- λ(x:A).t
lamP :: Ident -> Term -> Doc
lamP x t =
    hang (char 'λ' <> ident x <> char '.')
         indentation (term t)

-- case x do { 'tagᵢ → tᵢ | i = 1..n }
caseP :: Ident -> [(String, Term)] -> Doc
caseP x l =
    text "case" <+> ident x <+> text "do" $+$
    (sep $ map f l)
    where
      f (s,t) = hang (text s <+> char '→') indentation (term t)


-- let i = d in t
letP :: Doc -> Doc -> Doc -> Doc
letP i d t =
    text "let" <+> i $+$
    nest indentation d $+$ text "in" $+$
    nest indentation t

letP1 :: Ident -> Doc -> Doc -> Doc
letP1 i = letP (ident i)

letP2 :: Ident -> Ident -> Doc -> Doc -> Doc
letP2 i1 i2 = letP $ pairP i1 i2

star :: Doc
star = text "★"

scriptPretty :: String -> Int -> Doc
scriptPretty s = text . scriptShow s

scriptShow (minus:digits) x = if x < 0 then minus : sho (negate x) else sho x
  where sho x = showIntAtBase 10 (\i -> digits !! i) x []

subscriptPretty = scriptPretty "-₀₁₂₃₄₅₆₇₈₉"

sort :: Int -> Doc
sort s = star <> subscriptPretty s

term :: Term -> Doc
term (t,_) =
    case t of
      Var i -> ident i

      Pi i s x tyA tyB t' ->
          letP (varsort i s) (piP x tyA tyB) (term t')
      Lam i ty x tfun t' ->
          letP (vartype i ty) (lamP x tfun) (term t')
      App i f x t' ->
          letP1 i (ident f <+> ident x) (term t')

      Sigma i s x tyA tyB t' ->
          letP (varsort i s) (sigmaP x tyA tyB) (term t')
      Pair i ty x y t' ->
          letP (vartype i ty) (pairP x y) (term t')
      Proj i1 i2 z t' ->
          letP2 i1 i2 (ident z) (term t')

      Fin i l t' ->
          letP1 i (finP l) (term t')
      Tag i ty s t' -> letP (vartype i ty) (text s) (term t')
      Case x l -> caseP x l
      Star i -> sort i
