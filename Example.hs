{-# LANGUAGE DeriveGeneric #-}

import Sexp
import Control.Monad.Error
import qualified System.Environment as Environment

data Foo = A | B deriving (Show, Generic)
instance OfSexp Foo
instance ToSexp Foo

data Bar = C String | D Foo Foo deriving (Show, Generic)
instance OfSexp Bar
instance ToSexp Bar

data Baz = Z { field :: String } | Y { field :: String, yyy :: Baz } deriving (Show, Generic)
instance OfSexp Baz
instance ToSexp Baz

data Goo = G1 Goo | G2 deriving (Show, Generic)
instance OfSexp Goo
instance ToSexp Goo

data Type = Foo | Bar | Baz | Goo deriving (Show, Generic)
instance OfSexp Type

type_of_string :: String -> SexpResult Type
type_of_string = of_sexp . Atom

show_error :: Show e => Either e a -> Either String a
show_error = either (Left . show) (Right . id)

errorT :: Monad m => Either e a -> ErrorT e m a
errorT r = ErrorT $ return r

parse_args :: ErrorT String IO (Type, Sexp)
parse_args = do
  args <- liftIO Environment.getArgs
  case args of
    [s_type, s_sexp] -> do
      type_ <- errorT $ show_error $ type_of_string s_type
      sexp  <- errorT $ read_result s_sexp
      return (type_, sexp)
    _ -> do
      prog <- liftIO Environment.getProgName
      throwError $ prog ++ " <foo|bar|baz|goo> <sexp>"

unsexp_and_resexp :: Type -> Sexp -> SexpResult Sexp
unsexp_and_resexp Foo sexp = fmap to_sexp (of_sexp sexp :: SexpResult Foo)
unsexp_and_resexp Bar sexp = fmap to_sexp (of_sexp sexp :: SexpResult Bar)
unsexp_and_resexp Baz sexp = fmap to_sexp (of_sexp sexp :: SexpResult Baz)
unsexp_and_resexp Goo sexp = fmap to_sexp (of_sexp sexp :: SexpResult Goo)

main :: IO ()
main = do
  res <- runErrorT $ get_result
  case res of
    Left  error -> putStrLn error
    Right sexp -> putStrLn $ show sexp
  where
    get_result = do
      (type_, sexp) <- parse_args
      errorT $ show_error $ unsexp_and_resexp type_ sexp

