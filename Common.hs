module Common (module Common, E.throwError, E.catchError) where

import Data.List(partition)
import PPrint
import NormalForm(NF,Type)
import Names
import Data.Functor.Identity
import Control.Monad.Error as E
import Control.Monad.Writer hiding ((<>))

-- | General errors

instance Error Doc where
    strMsg s = text s

type Err = ErrorT Doc (WriterT [Doc] IO)

returnErr :: Pretty a => Int -> Err a -> IO ()
returnErr n t = do
  (res,trace) <- runWriterT $ runErrorT t
  case res of
    Left x -> print $ pretty (x $+$ selectLast n trace)
    Right x -> print (pretty x)


-- | Type errors

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

type TypeError a = ErrorT TypeInfo (Writer [Doc]) a

runTypeError :: TypeError a -> (Either TypeInfo a, [Doc])
runTypeError x = runWriter $ runErrorT x

report :: Doc -> TypeError ()
report x = tell [x]

convert :: TypeError a -> Err a
convert =
    mapErrorT $ mapWriterT (f . runIdentity)
        where f (x,trace) = return $ (lmap pretty x, trace)
              lmap g (Left x) = Left $ g x
              lmap _ (Right x) = Right x

selectLast :: Int -> [Doc] -> Doc
selectLast _ [] = empty
selectLast x l =
    text "While :" $$ (pretty $ take x l)


-- | Type errors formating.

introError :: Ident -> Doc
introError i =
    text "at position" <+> pretty (getPos i) <+> colon

introError' :: Type -> Doc
introError' t = pretty t

instance Pretty TypeInfo where
  pretty e = case e of
    Unification x y ->
        introError' x <&> introError' y $+$
        text "Type error during the unification of"
        <+> pretty x <+> text "and" <+> pretty y <> char '.'
    SubSort x y ->
        introError' x <&> introError' y  $+$
        text "Type" <+> pretty x <+>
        text "should be a subsort of" <+> pretty y <> char '.'
    Check i ty s  ->
        introError i <&> introError' ty $+$
        text "Type error during the checking of "
        <+> pretty i <+> text "with type" <+> pretty ty
        <+> colon <+> text s
    Normalize ty s  ->
        pretty ty $+$
        text "Type error during normalization of "
        <+> pretty ty <+> colon <+> text s
    Abstract i ->
        introError i $+$
        text "This term is abstract and can't be decomposed :"
        <+> pretty i
    IncompBindings i ty ty' ->
        introError i $+$
        text "Types" <+> pretty ty <+> text "and"
        <+> pretty ty' <+> text "for variable"
        <+> pretty i <+> text "are incompatibles."
    UnknownError s -> s


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
