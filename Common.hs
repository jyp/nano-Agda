module Common where

import PPrint
import Terms
import Names
import Control.Monad.Error as E

 -- General error

type Err = ErrorT String IO

 -- Typing error

data TypeInfo
    = Unification Ident Ident
    | Check Ident Ident String
    | IncompBindings Ident Type Type
    | Abstract Ident
    | UnknownError String

instance Error TypeInfo where
    strMsg s = UnknownError s

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
          "Type error during the unification of "
          ++ show x ++ " and " ++ show y
      Check i ty s  ->
          throw $
          "Type error during the checking of "
          ++ show i ++ " with type " ++ show ty ++ " : " ++ s
      Abstract ty ->
          throw $
          "This term is abstract and can't be decomposed : "
          ++ show ty
      IncompBindings i ty ty' ->
          throw $
          "Types" ++ show ty ++ " and " ++ show ty' ++
           " for variable " ++ show i ++ " are incompatibles."
      UnknownError s -> throw s


-- A fold/map hybrid to pass along the environment.
scanfoldl :: Monad m => (env -> a -> m (env, b)) -> env -> [a] -> m (env, [b])
scanfoldl = aux [] where
    aux acc _ e [] = return (e,acc)
    aux acc f e (h:t) = do
      (e',h') <- f e h
      aux (h':acc) f e' t
