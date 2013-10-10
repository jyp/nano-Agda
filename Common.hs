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
    | CheckT Term Type
    | CheckI Ident Type
    | IncompBindings Ident Term Term
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
      CheckT t ty ->
          throw $
          "Type error during the checking of "
          ++ (show $ term t) ++ " with type " ++ (show $ term ty)
      CheckI i ty ->
          throw $
          "Type error during the checking of "
          ++ show i ++ " with type " ++ (show $ term ty)
      UnknownError s -> throw s
