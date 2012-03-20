{-# LANGUAGE PackageImports, GADTs, KindSignatures, StandaloneDeriving, EmptyDataDecls, FlexibleInstances, OverloadedStrings #-}

module Terms(Ident, Irr(..), Identifier(..), Sort(..), 
             Term(..), 
--                 bound, app, proj, 
                      prettyTerm,
             Position, dummyPosition, identPosition, termPosition,
             isDummyId, synthId, dummyId, 
--             destruction,
            -- wk, wkn, subst0, ssubst
            ) where

import Prelude hiding (length, elem,foldl)
import Basics 
import Display
import Data.Sequence hiding (zip,replicate,reverse)
import Control.Arrow (second)
import Data.Foldable

data Term :: * where
     Hole :: Irr Position -> String -> Term -- placeholder
     Star :: Irr Position -> Sort -> Term -- sort
     Bound :: Irr Position -> Int -> Term -- variable
     Pi :: Ident -> Term -> Term -> Term 
     Sigma :: Ident -> Term -> Term -> Term
     Lam :: Ident -> Term -> Term -> Term 
     Pair :: Ident -> Term -> Term -> Term 
     (:$:) :: Term -> Term -> Term -- application
     -- 1st projection.
     Proj :: Term -> String -> Term     
     -- 2nd projection.     
     Extr :: Term -> String -> Term 
     
     -- Type annotation. Not present in normal forms.
     Ann :: Term -> Term -> Term 
     
-- | Position of a term, for error-reporting
termPosition :: Term -> Irr Position 
termPosition (Hole p _) = p
termPosition (Star p _) = p
termPosition (Bound p _) = p
termPosition (Pi i _ _) = identPosition i
termPosition (Sigma i _ _) = identPosition i
termPosition (Lam i _ _) = identPosition i
termPosition (Pair i _ _) = identPosition i
termPosition (x :$: y) = termPosition x
termPosition (Proj x _) = termPosition x
termPosition (Extr x _) = termPosition x
termPosition (Ann x _) = termPosition x

deriving instance Show (Term)
deriving instance Eq (Term)

dec xs = [ x - 1 | x <- xs, x > 0]

freeVars :: Term -> [Int]
freeVars (Ann a b) = freeVars a <> freeVars b
freeVars (Pi _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (Sigma _ a b) = freeVars a <> (dec $ freeVars b)
freeVars (Bound _ x) = [x]
freeVars (a :$: b) = freeVars a <> freeVars b
freeVars (Lam _ ty b) = freeVars ty <> (dec $ freeVars b)
freeVars (Star _ _) = mempty
freeVars (Hole _ _) = mempty
freeVars (Pair _ x y) = freeVars x <> (dec $ freeVars y)
freeVars (Proj x _) = freeVars x
freeVars (Extr y _) = freeVars y

iOccursIn :: Int -> Term -> Bool
iOccursIn x t = x `elem` (freeVars t)

----------------------------
-- Display

cPrint :: Int -> DisplayContext -> Term -> Doc

cPrint p ii (Hole _ x) = text x
cPrint p ii (Star _ i) = pretty i
cPrint p ii (Bound _ k) 
  | k < 0 || k >= length ii  = text "<deBrujn index" <+> pretty k <+> text "out of range>"
  | otherwise = pretty (ii `index` k)
cPrint p ii (Proj x f)     = cPrint p ii x <> "#" <> text f
cPrint p ii (Extr x f)     = cPrint p ii x <> "/" <> text f
cPrint p ii t@(_ :$: _)     = let (fct,args) = nestedApp t in 
                                 parensIf (p > 3) (cPrint 3 ii fct <+> sep (map (cPrint 4 ii) args))
cPrint p ii (Pi name d r)    = parensIf (p > 1) (sep [printBind ii name d r <+> "->", cPrint 1 (name <| ii) r])
                                 
cPrint p ii (Sigma name d r) = parensIf (p > 1) (sep [printBind ii name d r <+> text "×",  cPrint 1 (name <| ii) r])
cPrint p ii (t@(Lam _ _ _))   = parensIf (p > 1) (nestedLams ii mempty t)
cPrint p ii (Ann c ty)      = parensIf (p > 0) (cPrint 1 ii c <+> text ":" <+> cPrint 0 ii ty)
cPrint p ii (Pair name x y) = parensIf (p > (-1)) (sep [pretty name <+> text "=" <+> cPrint 0 ii x <> comma, cPrint (-1) (name <| ii) y])

nestedLams :: DisplayContext -> Seq Doc -> Term -> Doc
nestedLams ii xs (Lam x (Hole _ _) c) = nestedLams (x <| ii) (xs |> pretty x) c
nestedLams ii xs (Lam x ty c) = nestedLams (x <| ii) (xs |> parens (pretty x <+> ":" <+> cPrint 0 ii ty)) c
nestedLams ii xs t         = (text "\\ " <> (sep $ toList $ xs) <+> text "->" <+> nest 3 (cPrint 0 ii t))

printBind ii name d r = case not (isDummyId name) ||  0 `iOccursIn` r of
                  True -> parens (pretty name <+> text ":" <+> cPrint 0 ii d)
                  False -> cPrint 2 ii d

nestedApp :: Term -> (Term,[Term])
nestedApp (f :$: a) = (second (++ [a])) (nestedApp f)
nestedApp t = (t,[])

prettyTerm = cPrint (-100)

instance Pretty Term where
    pretty = prettyTerm mempty

