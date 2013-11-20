module Common where

import Data.List(partition)
import PPrint
import Terms
import NormalForm(NF,Type)
import Names
import Control.Monad.Error as E

import Text.PrettyPrint

 -- General error

type Err = ErrorT Doc IO

instance Error Doc where
    strMsg s = text s

 -- Typing error

data TypeInfo
    = Unification Type Type
    | SubSort Type Type
    | Check Ident Type String
    | IncompBindings Ident Type Type
    | Abstract Ident
    | UnknownError Doc
    | Normalize NF String

instance Error TypeInfo where
    strMsg s = UnknownError $ text s

type TypeError = Either TypeInfo

throw :: MonadError e m => e -> m a
throw = E.throwError

catch :: MonadError e m => m a -> (e -> m a) -> m a
catch = E.catchError

introError :: Ident -> Doc
introError (_,_,p) =
    text "at position" <+> pretty p <+> colon

introError' :: Type -> Doc
introError' t = pretty t

convert :: TypeError a -> Err a
convert (Right x) = return x
convert (Left e) =
    case e of
      Unification x y ->
          throw $
          introError' x <&> introError' y $+$
          text "Type error during the unification of"
          <+> pretty x <+> text "and" <+> pretty y <> char '.'
      SubSort x y ->
          throw $
          introError' x <&> introError' y  $+$
          text "Type" <+> pretty x <+>
          text "should be a subsort of" <+> pretty y <> char '.'
      Check i ty s  ->
          throw $
          introError i <&> introError' ty $+$
          text "Type error during the checking of "
          <+> pretty i <+> text "with type" <+> pretty ty
          <+> colon <+> text s
      Normalize ty s  ->
          throw $
          pretty ty $+$
          text "Type error during normalization of "
          <+> pretty ty <+> colon <+> text s
      Abstract i ->
          throw $
          introError i $+$
          text "This term is abstract and can't be decomposed :"
          <+> pretty i
      IncompBindings i ty ty' ->
          throw $
          introError i $+$
          text "Types" <+> pretty ty <+> text "and"
          <+> pretty ty' <+> text "for variable"
          <+> pretty i <+> text "are incompatibles."
      UnknownError s -> throw s


-- A fold/map hybrid to pass along the environment.
scanfoldl :: Monad m => (env -> a -> m (env, b)) -> env -> [a] -> m (env, [b])
scanfoldl f e l = do
  (e',l') <- aux [] f e l
  return (e', reverse l')
      where
        aux acc' _ e' [] = return (e',acc')
        aux acc' f' e' (h:t) = do
                  (e'',h'') <- f' e' h
                  aux (h'':acc') f' e'' t

-- Stable grouping function
groupAllBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupAllBy eq l =
     reverse $ f l [] where
        f [] acc = acc
        f (h:t) acc =
          let (same, other) = partition (eq h) t in
          f other ((h:same) : acc)
