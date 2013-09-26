module PPrint where

import Names
import Terms

import Text.PrettyPrint

-- default indentation
indentation :: Int
indentation = 2

ident :: Ident -> Doc
ident (i,n,_) = text n <> int i

-- x:A
vartype :: Ident -> Term -> Doc
vartype x tyA = ident x <> colon <> term tyA

-- (x:A)×B
sigmaP :: Ident -> Term -> Term -> Doc
sigmaP x tyA tyB = parens (vartype x tyA) <> text "×" <> term tyB

-- (x:A)→B
piP :: Ident -> Term -> Term -> Doc
piP x tyA tyB = parens (vartype x tyA) <> text "→" <> term tyB

-- { 'tag₁ , ... 'tagₙ }
finP :: [String] -> Doc
finP l = sep $ punctuate (char ',') $ map text l

-- (x,y)
pairP :: Ident -> Ident -> Doc
pairP x y = parens (ident x <> text ", " <> ident y)

-- λ(x:A).t
lamP :: Ident -> Term -> Term -> Doc
lamP x tyA t =
    hang (char 'λ' <> vartype x tyA <> char '.')
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


term :: Term -> Doc
term (t,_) =
    case t of
      Var i -> ident i

      Pi i x tyA tyB t' ->
          letP1 i (piP x tyA tyB) (term t')
      Lam i x tyA tfun t' ->
          letP1 i (lamP x tyA tfun) (term t')
      App i f x t' ->
          letP1 i (ident f <+> ident x) (term t')

      Sigma i x tyA tyB t' ->
          letP1 i (sigmaP x tyA tyB) (term t')
      Pair i x y t' ->
          letP1 i (pairP x y) (term t')
      Proj i1 i2 z t' ->
          letP2 i1 i2 (ident z) (term t')

      Fin i l t' ->
          letP1 i (finP l) (term t')
      Tag s -> text s
      Case x l -> caseP x l
