{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Sexp (
  Sexp(..),
  SexpResult(..),
  ToSexp(..),
  OfSexp(..),
  Generic
) where

import Data.Char as Char
import Data.List( (\\) )
import Data.Either( partitionEithers )
import GHC.Generics

data Sexp = 
    Atom String 
  | List [Sexp]
  deriving (Eq, Ord, Generic)
           
sexp_symbol_char '(' = False
sexp_symbol_char ')' = False
sexp_symbol_char  c  = not (Char.isSpace c)

instance Show Sexp where
  showsPrec _ (Atom x) s  = 
    if all (\c -> Char.isPrint c && sexp_symbol_char c) x then 
      x ++ s 
    else 
      shows x s
  showsPrec _ (List []) s = "()" ++ s
  showsPrec _ (List (x:xs)) s = "(" ++ shows x (show_rest xs (")" ++ s))
    where show_rest []     s = s
          show_rest (x:xs) s = " " ++ shows x (show_rest xs s)          

instance Read Sexp where
   readsPrec _ ""        = []
   readsPrec _ ( c : cs) | Char.isSpace c = reads cs
   readsPrec _ (')': _ ) = []
   readsPrec _ ('(':')': cs) = [(List [], cs)]
   readsPrec _ ('(':     cs) = do
     (next,      rest)  <- reads cs
     (List rest, rest') <- reads ('(' : rest)
     return (List (next : rest), rest')
   readsPrec _ s@('"': _ ) = map (\(s, rest) -> (Atom s, rest)) $ reads s
   readsPrec _ s = 
     let (atom, rest) = span sexp_symbol_char s in
     [(Atom atom, rest)]

class GenericToSexp f where
  generic_to_sexp :: f p -> [Sexp]
  
instance (Datatype c, GenericToSexp a) => GenericToSexp (M1 D c a) where
  generic_to_sexp (M1 x) = generic_to_sexp x  

instance (Constructor c, GenericToSexp a) => GenericToSexp (M1 C c a) where
  generic_to_sexp x = 
    let constr = Atom (conName x) in
    case generic_to_sexp (unM1 x) of
      []    -> [constr]
      args  -> [List (constr : args)]

instance (Selector c, GenericToSexp a) => GenericToSexp (M1 S c a) where
  generic_to_sexp x = 
    let value = generic_to_sexp (unM1 x) in
    case selName x of
      ""   -> value
      name -> [List (Atom name : value)]
  
instance GenericToSexp U1 where
  generic_to_sexp U1 = []
  
instance (GenericToSexp a, GenericToSexp b) => GenericToSexp (a :+: b) where
  generic_to_sexp (L1 x) = generic_to_sexp x
  generic_to_sexp (R1 x) = generic_to_sexp x

instance (GenericToSexp a, GenericToSexp b) => GenericToSexp (a :*: b) where
  generic_to_sexp (a :*: b) = generic_to_sexp a ++ generic_to_sexp b
  
instance ToSexp a => GenericToSexp (K1 i a) where
  generic_to_sexp (K1 x) = [to_sexp x]
  
class ToSexp a where
  to_sexp :: a -> Sexp
  list_to_sexp :: [a] -> Sexp
  list_to_sexp xs = List (map to_sexp xs)
  
  default to_sexp :: (Generic a, GenericToSexp (Rep a)) => a -> Sexp
  to_sexp = head . generic_to_sexp . from
  

data SexpResult a = 
    Error Sexp String 
  | Success a deriving (Show, Eq)
                   
instance Functor SexpResult where
  fmap f (Error m s) = Error m s
  fmap f (Success x) = Success (f x)
  
instance Monad SexpResult where
  (Error m s) >>= f = Error m s
  (Success a) >>= f = f a
  return = Success
  fail   = Error (Atom "<sexp not supplied>")
  
data Arguments x = NotLabeled Int | Labeled [String] deriving Show

combineArguments :: Arguments a -> Arguments b -> Arguments c
combineArguments  (NotLabeled a) (NotLabeled b) = NotLabeled (a +  b)
combineArguments  (Labeled    a) (Labeled    b) = Labeled    (a ++ b)
combineArguments _ _ = error "combineArguments"

class ArgumentCount f where
  arguments :: Arguments (f p)
  
instance ArgumentCount U1 where
  arguments = NotLabeled 0

instance (ArgumentCount a, ArgumentCount b) => ArgumentCount (a :*: b) where
  arguments = combineArguments a b :: Arguments ((a :*: b) p)
    where a = arguments :: Arguments (a p)
          b = arguments :: Arguments (b p)

instance (Selector c) => ArgumentCount (M1 S c a) where
  arguments  =
    case selName m1 of
      ""  -> NotLabeled 1
      lbl -> Labeled [lbl]
    -- Need -XScopedTypeVariables here:
    where m1 = undefined :: M1 S c a p

class GenericOfSexp f where
  generic_of_sexp :: Sexp -> SexpResult (f p)
  
instance GenericOfSexp U1 where 
  generic_of_sexp _ = Success U1
  
instance (Datatype c, GenericOfSexp a) => GenericOfSexp (M1 D c a) where
  generic_of_sexp sexp    = fmap M1 $ generic_of_sexp sexp
  
instance (Constructor c, ArgumentCount a, GenericOfSexp a) => GenericOfSexp (M1 C c a) where
  generic_of_sexp sexp = 
    do input_args   <- match_constructor_and_get_args
       ordered_args <- order_args input_args
       fmap M1 $ generic_of_sexp (case ordered_args of 
                                     [x] -> x 
                                     _   -> List ordered_args)
    where 
      m1 = undefined :: M1 C c a p
      constructor_matches c = 
        (map Char.toLower $ conName m1) == (map Char.toLower c)
      match_constructor_and_get_args = 
        case sexp of
          Atom c               | constructor_matches c -> Success []
          List (Atom c : args) | constructor_matches c -> Success args
          Atom _               | otherwise -> Error sexp $ "expected " ++ conName m1
          List (Atom c : _)    | otherwise -> Error sexp $ "expected " ++ conName m1
          List _ -> Error sexp "expected a constructor"
      order_args input_args =
        case arguments :: Arguments (a p) of
          NotLabeled n | length input_args == n -> Success input_args
          NotLabeled n | otherwise -> Error sexp ("expected "++show n++" arguments")
          Labeled labels ->
            let 
              parse_field (List [Atom field, value]) = Success (field, value)
              parse_field sexp = Error sexp "not a record field"
              error_message inputs = 
                if null missing then "extra fields: " ++ show extra
                else "missing fields: " ++ show missing 
                     ++ if null extra then "" else "; extra fields: " ++ show extra
                where missing = labels \\ inputs
                      extra   = inputs \\ labels
            in 
            do input_args' <- mapM parse_field input_args
               let error = Error sexp (error_message $ map fst input_args') in  
                 if length input_args' /= length labels then
                   error
                 else
                   maybe error Success $ mapM (flip lookup input_args') labels
      
instance (GenericOfSexp a, GenericOfSexp b) => GenericOfSexp (a :+: b) where
  generic_of_sexp sexp = 
    case left of
      Success x -> Success (L1 x)
      Error _ m -> 
        case right of
          Success x  -> Success (R1 x)
          Error _ m' -> Error sexp (m ++ " or " ++ m')
    where
      left   = generic_of_sexp sexp
      right  = generic_of_sexp sexp
      
instance (GenericOfSexp a, GenericOfSexp b) => GenericOfSexp (a :*: b) where
  generic_of_sexp sexp@(Atom _)  = error "BUG: using atom to unsexp a product"
  generic_of_sexp sexp@(List []) = error "BUG: using () to unsexp a product"
  generic_of_sexp sexp@(List (a : b)) =
    do a' <- generic_of_sexp a
       b' <- (case b of 
                 [b] -> generic_of_sexp b 
                 _   -> generic_of_sexp (List b))
       return $ a' :*: b'
      
instance (Selector c, GenericOfSexp a) => GenericOfSexp (M1 S c a) where
  generic_of_sexp sexp = fmap M1 $ generic_of_sexp sexp
      
instance OfSexp a => GenericOfSexp (K1 c a) where
  generic_of_sexp sexp = (fmap K1 $ of_sexp sexp)

class OfSexp a where
  of_sexp :: Sexp -> SexpResult a
  list_of_sexp :: Sexp -> SexpResult [a]
  list_of_sexp (List sexps)  = mapM of_sexp sexps
  list_of_sexp sexp@(Atom _) = Error sexp "expected a list"
  
  default of_sexp :: (Generic a, GenericOfSexp (Rep a)) => Sexp -> SexpResult a
  of_sexp sexp = fmap to $ generic_of_sexp sexp

instance ToSexp () where
  to_sexp () = List []
instance OfSexp () where
  of_sexp (List []) = Success ()
  of_sexp sexp      = Error sexp "expected a Unit value"
  
instance ToSexp a => ToSexp (Maybe a) where
  to_sexp Nothing  = List []
  to_sexp (Just x) = List [to_sexp x]
instance OfSexp a => OfSexp (Maybe a) where
  of_sexp (List [])  = Success Nothing
  of_sexp (List [x]) = fmap Just $ of_sexp x
  of_sexp sexp       = Error sexp "expected a Maybe value"

instance ToSexp Char where
  to_sexp c = Atom ([c])
  list_to_sexp s = Atom s
instance OfSexp Char where
  of_sexp (Atom [c]) = Success c
  of_sexp sexp@(List _) = Error sexp "expected an atom"
  list_of_sexp (Atom s)      = Success s
  list_of_sexp sexp@(List _) = Error sexp "expected an atom" 

instance ToSexp a => ToSexp [a] where
  to_sexp = list_to_sexp
instance OfSexp a => OfSexp [a] where
  of_sexp = list_of_sexp
  
tuple_of_sexp_error _ sexp@(Atom _) = Error sexp "expected a list"
tuple_of_sexp_error n sexp@(List _) = Error sexp $ "expected "++show n++" elements"
  
instance (ToSexp a, ToSexp b) => ToSexp (a, b) where
  to_sexp (a, b) = List [to_sexp a, to_sexp b]
instance (OfSexp a, OfSexp b) => OfSexp (a, b) where
  of_sexp (List [a, b]) = 
    do a' <- of_sexp a  
       b' <- of_sexp b 
       return (a', b')
  of_sexp sexp = tuple_of_sexp_error 2 sexp

instance (ToSexp a, ToSexp b, ToSexp c) => ToSexp (a, b, c) where
  to_sexp (a, b, c) = List [to_sexp a, to_sexp b, to_sexp c]
instance (OfSexp a, OfSexp b, OfSexp c) => OfSexp (a, b, c) where
  of_sexp (List [a, b, c]) = 
    do a' <- of_sexp a  
       b' <- of_sexp b 
       c' <- of_sexp c
       return (a', b', c')
  of_sexp sexp = tuple_of_sexp_error 3 sexp

instance (ToSexp a, ToSexp b, ToSexp c, ToSexp d) => ToSexp (a, b, c, d) where
  to_sexp (a, b, c, d) = List [to_sexp a, to_sexp b, to_sexp c, to_sexp d]
instance (OfSexp a, OfSexp b, OfSexp c, OfSexp d) => OfSexp (a, b, c, d) where
  of_sexp (List [a, b, c, d]) = 
    do a' <- of_sexp a  
       b' <- of_sexp b 
       c' <- of_sexp c
       d' <- of_sexp d
       return (a', b', c', d')
  of_sexp sexp = tuple_of_sexp_error 4 sexp

instance ToSexp Bool
instance OfSexp Bool

instance ToSexp Ordering
instance OfSexp Ordering

instance (ToSexp a, ToSexp b) => ToSexp (Either a b)
instance (OfSexp a, OfSexp b) => OfSexp (Either a b)


-- I can't do this:
-- class Show a => ToSexpWithShow a
-- instance ToSexpWithShow a => ToSexp a where
--   to_sexp = Atom . show
-- instance ToSexpWithShow Int
-- instance ToSexpWithShow Integer
-- instance ToSexpWithShow Float
-- instance ToSexpWithShow Double

-- and I can't do this:
-- instance (Show x, Num x) => ToSexp x where
--   to_sexp = Atom . show

to_sexp_show x = Atom $ show x

of_sexp_read sexp@(Atom x) = 
  let parses = map fst . filter (null . snd) $ reads x in
  case parses of
    [x] -> Success x
    []  -> Error sexp "no parse"
    _   -> Error sexp "ambiguous parse"
of_sexp_read sexp@(List _) =  
  Error sexp "expected an atom"

instance ToSexp Int where
  to_sexp = to_sexp_show
instance ToSexp Integer where
  to_sexp = to_sexp_show
instance ToSexp Float where
  to_sexp = to_sexp_show
instance ToSexp Double where
  to_sexp = to_sexp_show

instance OfSexp Int where
  of_sexp = of_sexp_read
instance OfSexp Integer where
  of_sexp = of_sexp_read
instance OfSexp Float where
  of_sexp = of_sexp_read
instance OfSexp Double where
  of_sexp = of_sexp_read

{- -- examples
  
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

data Alist a b = Alist [(a, b)]  deriving (Show, Generic)
instance (OfSexp a, OfSexp b) => OfSexp (Alist a b)
instance (ToSexp a, ToSexp b) => ToSexp (Alist a b)

-}