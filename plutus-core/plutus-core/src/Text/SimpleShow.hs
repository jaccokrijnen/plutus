{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}
module Text.SimpleShow
  ( SimpleShow (..)
  , parens
  ) where

import Data.ByteString (ByteString)
import Data.Set (Set, toList)
import Data.Text (Text, pack, unpack)
import GHC.Generics
import GHC.Word


parens :: Bool -> Text -> Text
parens True x  = "(" <> x <> ")"
parens False x = x

-- Used to determine if a constructor is applied to any arguments, if so, it
-- will need parentheses when printing

class GIsApplied f where
  gIsApplied :: f a -> Bool

instance GIsApplied U1 where
  gIsApplied _ = False

instance GIsApplied V1 where
  gIsApplied _ = False

instance GIsApplied (K1 i c) where
  gIsApplied _ = True

instance (GIsApplied f) => GIsApplied (M1 D c f) where
  gIsApplied (M1 x) = gIsApplied x

instance (GIsApplied f) => GIsApplied (M1 C c f) where
  gIsApplied (M1 x) = gIsApplied x

instance (GIsApplied f) => GIsApplied (M1 S c f) where
  gIsApplied (M1 x) = gIsApplied x

instance GIsApplied (f :*: g) where
  gIsApplied _ = True

instance (GIsApplied f, GIsApplied g) => GIsApplied (f :+: g) where
  gIsApplied (L1 x) = gIsApplied x
  gIsApplied (R1 x) = gIsApplied x



class SimpleShow a where
  simpleShow :: a -> Text

  default simpleShow :: (Generic a, SimpleShow' (Rep a)) => a -> Text
  simpleShow x = simpleShow' (from x)

class SimpleShow' f where
  simpleShow' :: f a -> Text

instance SimpleShow' U1 where
  simpleShow' U1 = ""

instance (SimpleShow' f, SimpleShow' g) => SimpleShow' (f :*: g) where
  simpleShow' (x :*: y) = simpleShow' x <> " " <> simpleShow' y

instance (SimpleShow' f, SimpleShow' g) => SimpleShow' (f :+: g) where
  simpleShow' (L1 x) = simpleShow' x
  simpleShow' (R1 x) = simpleShow' x

instance (SimpleShow' f) => SimpleShow' (M1 D c f) where
  simpleShow' (M1 x) = simpleShow' x

instance (SimpleShow' f, Constructor c, GIsApplied f) => SimpleShow' (M1 C c f) where
  simpleShow' m@(M1 x)
    | gIsApplied x = parens True $ pack (conName m) <> " " <> simpleShow' x
    | otherwise = pack (conName m)

instance (SimpleShow' f) => SimpleShow' (M1 S s f) where
  -- Ignore selector names
  simpleShow' (M1 x) = simpleShow' x

instance (SimpleShow a) => SimpleShow' (K1 i a) where
  simpleShow' (K1 x) = simpleShow x


instance SimpleShow Char where
  simpleShow = pack . show

instance SimpleShow Int where
  simpleShow = pack . show

instance SimpleShow Integer where
  simpleShow = pack . show

instance SimpleShow ByteString where
  simpleShow = pack . show

instance SimpleShow Bool where
  simpleShow = pack . show

-- instance {-# OVERLAPPING #-} SimpleShow Text where
--   simpleShow = show

instance SimpleShow Double where
  simpleShow = pack . show

instance SimpleShow Text where
  simpleShow = pack . show

instance SimpleShow (GHC.Word.Word64) where
  simpleShow = pack . show

instance SimpleShow a => SimpleShow (Set a) where
  simpleShow x = parens True ("Set " <> simpleShow (toList x))

instance (SimpleShow a, SimpleShow b) => SimpleShow (a, b) where
  simpleShow (a, b) = "(" <> simpleShow a <> ", " <> simpleShow b <> ")"


instance SimpleShow a => SimpleShow [a]

instance {-# OVERLAPPING #-} SimpleShow String where
  simpleShow = pack . show

-- Examples

data Person = Person { name :: Text, age :: Int, ints :: [Int]}
  deriving stock (Generic)

instance SimpleShow Person

data Shape = Circle Double | ShapePerson Person
  deriving stock (Generic)

instance SimpleShow Shape
_tests :: IO ()
_tests = do
  let person = Person "Alice" 30 [1,2,3]
  let shape1 = Circle 5.0
  let shape2 = ShapePerson person
  putStrLn . unpack $ simpleShow person
  putStrLn . unpack $ simpleShow shape1
  putStrLn . unpack $ simpleShow shape2

