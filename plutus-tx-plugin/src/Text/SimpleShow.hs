{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
module Text.SimpleShow where

import GHC.Generics

tests :: IO ()
tests = do
  let person = Person "Alice" 30 [1,2,3]
  let shape1 = Circle 5.0
  let shape2 = ShapePerson person
  putStrLn $ gshow person
  putStrLn $ gshow shape1
  putStrLn $ gshow shape2

parens :: Bool -> String -> String
parens True x  = "(" ++ x ++ ")"
parens False x = x

-- Used to determine if a constructor is applied to any arguments, if so, it
-- will need parentheses when printing
class IsApplied a where
  isApplied :: a -> Bool
  default isApplied :: (Generic a, GIsApplied (Rep a)) => a -> Bool
  isApplied x = gIsApplied (from x)

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

instance (GIsApplied f, GIsApplied g) => GIsApplied (f :*: g) where
  gIsApplied _ = True

instance (GIsApplied f, GIsApplied g) => GIsApplied (f :+: g) where
  gIsApplied (L1 x) = gIsApplied x
  gIsApplied (R1 x) = gIsApplied x



class ShowPrefix a where
  gshow :: a -> String

  default gshow :: (Generic a, ShowPrefix' (Rep a)) => a -> String
  gshow x = gshow' (from x)

class ShowPrefix' f where
  gshow' :: f a -> String

instance ShowPrefix' U1 where
  gshow' U1 = ""

instance (ShowPrefix' f, ShowPrefix' g) => ShowPrefix' (f :*: g) where
  gshow' (x :*: y) = gshow' x ++ " " ++ gshow' y

instance (ShowPrefix' f, ShowPrefix' g) => ShowPrefix' (f :+: g) where
  gshow' (L1 x) = gshow' x
  gshow' (R1 x) = gshow' x

instance (ShowPrefix' f) => ShowPrefix' (M1 D c f) where
  gshow' (M1 x) = gshow' x

instance (ShowPrefix' f, Constructor c, GIsApplied f) => ShowPrefix' (M1 C c f) where
  gshow' m@(M1 x)
    | gIsApplied x = parens True $ conName m ++ " " ++ gshow' x
    | otherwise = conName m

instance (ShowPrefix' f, Selector s) => ShowPrefix' (M1 S s f) where
  -- Ignore selector names
  gshow' (M1 x) = gshow' x

instance (ShowPrefix a) => ShowPrefix' (K1 i a) where
  gshow' (K1 x) = gshow x

instance ShowPrefix Char where
  gshow = show

instance ShowPrefix Int where
  gshow = show

instance ShowPrefix Bool where
  gshow = show

instance {-# OVERLAPPING #-} ShowPrefix String where
  gshow = show

instance ShowPrefix Double where
  gshow = show

instance (ShowPrefix a, ShowPrefix b) => ShowPrefix (a, b) where
  gshow (a, b) = "(" ++ gshow a ++ ", " ++ gshow b ++ ")"

instance ShowPrefix a => ShowPrefix [a]

data Person = Person { name :: String, age :: Int, ints :: [Int]}
  deriving (Generic)

instance ShowPrefix Person

data Shape = Circle Double | ShapePerson Person
  deriving (Generic)

instance ShowPrefix Shape

