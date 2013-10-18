module Common where

import Data.List(partition)
import PPrint
import Terms
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
    | Check Ident Ident String
    | IncompBindings Ident Type Type
    | Abstract Ident
    | UnknownError Doc

instance Error TypeInfo where
    strMsg s = UnknownError $ text s

type TypeError = Either TypeInfo

throw :: MonadError e m => e -> m a
throw = E.throwError

catch :: MonadError e m => m a -> (e -> m a) -> m a
catch = E.catchError

convert :: TypeError a -> Err a
convert (Right x) = return x
convert (Left e) =
    case e of
      Unification x y ->
          throw $
          text "Type error during the unification of"
          <+> pretty x <+> text "and" <+> pretty y <> char '.'
      SubSort x y ->
          throw $
          text "Type" <+> pretty x <+>
          text "should be a subsort of" <+> pretty y <> char '.'
      Check i ty s  ->
          throw $
          text "Type error during the checking of "
          <+> pretty i <+> text "with type" <+> pretty ty
          <+> colon <+> text s
      Abstract ty ->
          throw $
          text "This term is abstract and can't be decomposed :"
          <+> pretty ty
      IncompBindings i ty ty' ->
          throw $
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
