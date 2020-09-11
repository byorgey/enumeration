{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- SPDX-License-Identifier: BSD-3-Clause

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.CoEnumeration
-- Copyright   :  Brent Yorgey, Koji Miyazato
-- Maintainer  :  byorgey@gmail.com
-- 
-- A /coenumeration/ is a function from values to finite or countably infinite
-- sets, canonically represented by non-negative integers less than its cardinality.
-- 
-- Alternatively, a coenumeration can be thought of as a classification of values
-- into finite or countably infinite classes, with each class labelled with
-- integers.
-- 
-- This module provides many ways to construct @CoEnumeration@ values,
-- and most of them are implemented as inverses of enumerations made with
-- functions in "Data.Enumeration".
-- 
-- == Example
-- 
-- Through examples of this module, "Data.Enumeration" module is
-- referred by alias @E@.
-- 
-- > import qualified Data.Enumeration as E
-- 
-- >>> take 5 . drop 5 $ E.enumerate (E.listOf E.nat)
-- [[1,0],[2],[0,1],[1,0,0],[2,0]]
-- >>> locate (listOf nat) <$> [[1,0],[2],[0,1],[1,0,0],[2,0]]
-- [5,6,7,8,9]
--
-- >>> locate (listOf nat) [3,1,4,1,5,9,2]
-- 78651719792187121765701606023038613403478037124236785850350
-- >>> E.select (E.listOf E.nat) 78651719792187121765701606023038613403478037124236785850350
-- [3,1,4,1,5,9,2]
module Data.CoEnumeration
  ( -- * Coenumerations
    CoEnumeration(), card, locate, isFinite
  , unsafeMkCoEnumeration

    -- * Cardinality and Index
  , Index, Cardinality(..)

    -- * Primitive coenumerations
  , unit, lost
  , boundedEnum
  , nat
  , int
  , cw
  , rat

    -- * Coenumeration combinators
  , takeC, dropC, modulo, overlayC
  , infinite
  , (><), (<+>)
  , maybeOf, eitherOf, listOf, finiteSubsetOf
  , finiteFunctionOf

    -- * Utilities
  , unList, unSet
  ) where

import Data.Void
import Data.Bits
import Data.List (foldl')
import Data.Ratio

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible(lost, Divisible(..), Decidable(..))

import Data.Enumeration (Index, Cardinality(..))
import Data.Enumeration.Invertible (undiagonal)


------------------------------------------------------------
-- Setup for doctest examples
------------------------------------------------------------

-- $setup
-- >>> :set -XTypeApplications
-- >>> import qualified Data.Enumeration as E

-- | A /coenumeration/ is a function from values to finite or countably infinite
-- sets, canonically represented by non-negative integers less than its cardinality.
-- 
-- Alternatively, a coenumeration can be thought of as a classification of values
-- into finite or countably infinite classes, with each class labelled with
-- integers.
-- 
-- 'CoEnumeration' is an instance of the following type classes:
--
-- * 'Contravariant' (you can change the type of base values contravariantly)
-- * 'Divisible' (representing Cartesian product of finite number of coenumerations)
--
--     * Binary cartesian product ('><')
--     * Coenumeration onto singleton set as an unit ('unit')
--
-- * 'Decidable' (representing disjoint union of finite number of coenumerations)
--
--     * Binary disjoint union ('<+>')
--     * Coenumeration of uninhabited type 'Void'. It's not exported directly,
--       but only through a method of the class
--       
--         'lose' @:: Decidable f => (a -> Void) -> f Void@
--       
--         or
--       
--         'lost' @:: Decidable f => f Void@.
data CoEnumeration a = CoEnumeration
  { -- | Get the cardinality of a coenumeration.
    --   Under \"classification\" interpretation,
    --   it is the cardinality of the set of classes.
    card :: Cardinality

    -- | Compute the index of a particular value.
  , locate :: a -> Index
  }

-- | Returns if the the cardinality of coenumeration is finite.
isFinite :: CoEnumeration a -> Bool
isFinite = (Infinite /=) . card

-- | Constructs a coenumeration.
--
--   To construct valid coenumeration by @unsafeMkCoEnumeration n f@,
--   for all @x :: a@, it must satisfy @(Finite (f x) < n)@.
--   
--   This functions does not (and never could) check the validity
--   of its arguments.
unsafeMkCoEnumeration :: Cardinality -> (a -> Index) -> CoEnumeration a
unsafeMkCoEnumeration = CoEnumeration

instance Contravariant CoEnumeration where
  contramap f e = e{ locate = locate e . f }

-- | Associativity of 'divide' is maintained only when
--   arguments are finite.
instance Divisible CoEnumeration where
  divide f a b = contramap f $ a >< b
  conquer = unit

-- | Associativity of 'choose' is maintained only when
--   arguments are finite.
instance Decidable CoEnumeration where
  choose f a b = contramap f $ a <+> b
  lose f = contramap f void

-- | Coenumeration to the singleton set.
--
-- >>> card unit
-- Finite 1
-- >>> locate unit True
-- 0
-- >>> locate unit (3 :: Int)
-- 0
-- >>> locate unit (cos :: Float -> Float)
-- 0
unit :: CoEnumeration a
unit = CoEnumeration{ card = 1, locate = const 0 }

-- | Coenumeration of an uninhabited type 'Void'.
--
-- >>> card void
-- Finite 0
-- 
-- Note that when a coenumeration of a type @t@ has cardinality 0,
-- it should indicate /No/ value of @t@ can be created without
-- using bottoms like @undefined@.
void :: CoEnumeration Void
void = CoEnumeration{ card = 0, locate = const (error "locate void") }

-- | An inverse of forward 'E.boundedEnum'
boundedEnum :: forall a. (Enum a, Bounded a) => CoEnumeration a
boundedEnum = CoEnumeration{ card = size, locate = loc }
  where loc = toInteger . subtract lo . fromEnum
        lo = fromEnum (minBound @a)
        hi = fromEnum (maxBound @a)
        size = Finite $ 1 + toInteger hi - toInteger lo

-- | 'nat' is an inverse of forward enumeration 'E.nat'.
--  
-- For a negative integer @x@ which 'E.nat' doesn't enumerate,
-- @locate nat x@ returns the same index to the absolute value of @x@,
-- i.e. @locate nat x == locate nat (abs x)@.
-- 
-- >>> locate nat <$> [-3 .. 3]
-- [3,2,1,0,1,2,3]
nat :: CoEnumeration Integer
nat = CoEnumeration{ card = Infinite, locate = abs }

-- | 'int' is the inverse of forward enumeration 'E.int', which is
--   all integers ordered as the sequence @0, 1, -1, 2, -2, ...@
-- 
-- >>> locate int <$> [1, 2, 3, 4, 5]
-- [1,3,5,7,9]
-- >>> locate int <$> [0, -1 .. -5]
-- [0,2,4,6,8,10]
int :: CoEnumeration Integer
int = CoEnumeration{ card = Infinite, locate = integerToNat }
  where
    integerToNat :: Integer -> Integer
    integerToNat n
      | n <= 0    = 2 * negate n
      | otherwise = 2 * n - 1

-- | 'cw' is an inverse of forward enumeration 'E.cw'.
--
-- Because 'E.cw' only enumerates positive 'Rational' values,
-- @locate cw x@ for zero or less rational number @x@ could be arbitrary.
-- 
-- This implementation chose @locate cw x = 33448095@ for all @x <= 0@, which is
-- the index of @765 % 4321@, rather than returning @undefined@.
-- 
-- >>> locate cw <$> [1 % 1, 1 % 2, 2 % 1, 1 % 3, 3 % 2]
-- [0,1,2,3,4]
-- >>> locate cw (765 % 4321)
-- 33448095
-- >>> locate cw 0
-- 33448095
cw :: CoEnumeration Rational
cw = CoEnumeration{ card = Infinite, locate = locateCW }
  where
    locateCW x = case numerator x of
      n | n > 0     -> go n (denominator x) [] - 1
        | otherwise -> 33448095 {- Magic number, see the haddock above -}
    
    go 1 1 acc = foldl' (\i b -> 2 * i + b) 1 acc
    go a b acc
      | a > b = go (a - b) b (1 : acc)
      | a < b = go a (b - a) (0 : acc)
      | otherwise = error "cw: locateCW: Never reach here!"

-- | 'rat' is the inverse of forward enumeration 'E.rat'.
--
-- >>> let xs = E.enumerate . E.takeE 6 $ E.rat
-- >>> (xs, locate rat <$> xs)
-- ([0 % 1,1 % 1,(-1) % 1,1 % 2,(-1) % 2,2 % 1],[0,1,2,3,4,5])
-- >>> locate rat (E.select E.rat 1000)
-- 1000
rat :: CoEnumeration Rational
rat = contramap caseBySign $ maybeOf (cw <+> cw)
  where
    caseBySign :: Rational -> Maybe (Either Rational Rational)
    caseBySign x = case compare x 0 of
      LT -> Just (Right (negate x))
      EQ -> Nothing
      GT -> Just (Left x)

-- | Sets the cardinality of given coenumeration to 'Infinite'
infinite :: CoEnumeration a -> CoEnumeration a
infinite e = e{ card = Infinite }

-- | Cartesian product of coenumeration, made to be an inverse of
--   cartesian product of enumeration '(E.><)'.
--   
-- >>> let a  = E.finite 3 E.>< (E.boundedEnum @Bool)
-- >>> let a' = modulo 3     >< boundedEnum @Bool
-- >>> (E.enumerate a, locate a' <$> E.enumerate a)
-- ([(0,False),(0,True),(1,False),(1,True),(2,False),(2,True)],[0,1,2,3,4,5])
--
-- This operation is not associative if and only if one of arguments
-- is not finite.
(><) :: CoEnumeration a -> CoEnumeration b -> CoEnumeration (a,b)
e1 >< e2 = CoEnumeration{ card = n1 * n2, locate = locatePair }
  where
    n1 = card e1
    n2 = card e2
    locatePair = case (n1, n2) of
      (_,          Finite n2') -> \(a,b) -> locate e1 a * n2' + locate e2 b
      (Finite n1', Infinite)   -> \(a,b) -> locate e1 a + locate e2 b * n1'
      (Infinite,   Infinite)   -> \(a,b) -> undiagonal (locate e1 a, locate e2 b)

-- | Sum, or disjoint union, of two coenumerations.
--
--   It corresponds to disjoint union of enumerations 'E.eitherOf'.
--   
--   Its type can't be @CoEnumeration a -> CoEnumeration a -> CoEnumeration a@,
--   like 'Data.Enumeration.Enumeration' which is covariant functor,
--   because @CoEnumeration@ is 'Contravariant' functor.
--   
-- >>> let a  = E.finite 3 `E.eitherOf` (E.boundedEnum @Bool)
-- >>> let a' = modulo 3    <+>          boundedEnum @Bool
-- >>> (E.enumerate a, locate a' <$> E.enumerate a)
-- ([Left 0,Left 1,Left 2,Right False,Right True],[0,1,2,3,4])
--
-- This operation is not associative if and only if one of arguments
-- is not finite.
(<+>) :: CoEnumeration a -> CoEnumeration b -> CoEnumeration (Either a b)
e1 <+> e2 = CoEnumeration{ card = n1 + n2, locate = locateEither }
  where
    n1 = card e1
    n2 = card e2
    locateEither = case (n1, n2) of
      (Finite n1', _)          -> either (locate e1) ((n1' +) . locate e2)
      (Infinite,   Finite n2') -> either ((n2' +) . locate e1) (locate e2)
      (Infinite,   Infinite)   -> either ((*2) . locate e1) (succ . (*2) . locate e2)

-- |
--
-- >>> locate (dropC 3 nat) <$> [0..5]
-- [0,0,0,0,1,2]
dropC :: Integer -> CoEnumeration a -> CoEnumeration a
dropC k e
  | k == 0      = e
  | card e == 0 = e
  | card e <= Finite k = error "Impossible empty coenumeration"
  | otherwise = CoEnumeration{ card = size, locate = loc }
  where
    size = card e - Finite k
    loc = max 0 . subtract k . locate e

-- |
-- >>> locate (takeC 3 nat) <$> [0..5]
-- [0,1,2,2,2,2]
takeC :: Integer -> CoEnumeration a -> CoEnumeration a
takeC k
  | k <= 0 = checkEmpty
  | otherwise = aux
  where
    aux e =
      let size = min (Finite k) (card e)
          loc = min (k-1) . locate e
      in CoEnumeration{ card = size, locate = loc }

checkEmpty :: CoEnumeration a -> CoEnumeration a
checkEmpty e
  | card e == 0 = e
  | otherwise   = error "Impossible empty coenumeration"

-- |
-- >>> locate (modulo 3) <$> [0..7]
-- [0,1,2,0,1,2,0,1]
-- >>> locate (modulo 3) (-4)
-- 2
modulo :: Integer -> CoEnumeration Integer
modulo n
  | n <= 0    = error $ "modulo: invalid argument " ++ show n
  | otherwise = CoEnumeration{ card = Finite n, locate = (`mod` n) }

-- | @overlayC a b@ combines two coenumerations in parallel, sharing
--   indices of two coenumerations.
--
--   The resulting coenumeration has cardinality of the larger of the
--   two arguments.
overlayC :: CoEnumeration a -> CoEnumeration b -> CoEnumeration (Either a b)
overlayC e1 e2 = CoEnumeration{
    card = max (card e1) (card e2)
  , locate = either (locate e1) (locate e2)
  }

-- | The inverse of forward 'E.maybeOf'
maybeOf :: CoEnumeration a -> CoEnumeration (Maybe a)
maybeOf e = contramap (maybe (Left ()) Right) $ unit <+> e

-- | Synonym of '(<+>)'
eitherOf :: CoEnumeration a -> CoEnumeration b -> CoEnumeration (Either a b)
eitherOf = (<+>)

-- | Coenumerate all possible finite lists using given coenumeration.
--
--   If a coenumeration @a@ is the inverse of enumeration @b@,
--   'listOf' @a@ is the inverse of forward enumeration 'E.listOf' @b@.
-- 
-- >>> E.enumerate . E.takeE 6 $ E.listOf E.nat
-- [[],[0],[0,0],[1],[0,0,0],[1,0]]
-- >>> locate (listOf nat) <$> [[],[0],[0,0],[1],[0,0,0],[1,0]]
-- [0,1,2,3,4,5]
-- >>> E.select (E.listOf E.nat) 1000000
-- [1008,26,0]
-- >>> locate (listOf nat) [1008,26,0]
-- 1000000
listOf :: CoEnumeration a -> CoEnumeration [a]
listOf e = CoEnumeration{ card = size, locate = locateList }
  where
    n = card e
    size | n == 0    = 1
         | otherwise = Infinite
    locateList = unList n . fmap (locate e)

unList :: Cardinality -> [Index] -> Index
unList (Finite k) = foldl' (\n a -> 1 + (a + n * k)) 0 . reverse
unList Infinite   = foldl' (\n a -> 1 + undiagonal (a, n)) 0 . reverse

-- | An inverse of 'E.finiteSubsetOf'.
--
--   Given a coenumeration of @a@, make a coenumeration of finite sets of
--   @a@, by ignoring order and repetition from @[a]@.
-- 
-- >>> as = take 11 . E.enumerate $ E.finiteSubsetOf E.nat
-- >>> (as, locate (finiteSubsetOf nat) <$> as)
-- ([[],[0],[1],[0,1],[2],[0,2],[1,2],[0,1,2],[3],[0,3],[1,3]],[0,1,2,3,4,5,6,7,8,9,10])
finiteSubsetOf :: CoEnumeration a -> CoEnumeration [a]
finiteSubsetOf e = CoEnumeration{ card = size, locate = unSet . fmap (locate e) }
  where
    size = case card e of
      Finite k -> Finite (2 ^ k)
      Infinite -> Infinite

unSet :: [Index] -> Index
unSet = foldl' (\n i -> n .|. bit (fromInteger i)) 0

-- | An inverse of 'E.finiteEnumerationOf'.
--   
--   Given a coenumeration of @a@, make a coenumeration of function from
--   finite sets to @a@.
--   
--   Ideally, its type should be the following dependent type
--   
--   > {n :: Integer} -> CoEnumeration a -> CoEnumeration ({k :: Integer | k < n} -> a)
--
-- >>> let as = E.finiteEnumerationOf 3 (E.takeE 2 E.nat)
-- >>> map E.enumerate $ E.enumerate as
-- [[0,0,0],[0,0,1],[0,1,0],[0,1,1],[1,0,0],[1,0,1],[1,1,0],[1,1,1]]
-- >>> let inv_as = finiteFunctionOf 3 (takeC 2 nat)
-- >>> locate inv_as (E.select (E.finiteList [0,1,1]))
-- 3
finiteFunctionOf :: Integer -> CoEnumeration a -> CoEnumeration (Integer -> a)
finiteFunctionOf 0 _ = unit
finiteFunctionOf n a = CoEnumeration{ card = size, locate = locateEnum }
  where
    size = case card a of
      Finite k -> Finite (k^n)
      Infinite -> Infinite
    
    step = case card a of
      Finite k -> \r d -> k * r + d
      Infinite -> curry undiagonal

    locateEnum f =
      let go i !acc
            | i == n    = acc
            | otherwise = go (i+1) (step acc (locate a (f i)))
      in go 0 0
