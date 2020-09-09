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
-- TODO examples

-----------------------------------------------------------------------------

module Data.CoEnumeration
  ( -- * Coenumerations
    CoEnumeration(), card, locate
  , unsafeMkCoEnumeration

    -- * Cardinality and Index
  , Index, Cardinality(..), isFinite

    -- * Primitive coenumerations
  , unit, lost
  , boundedEnum
  , nat
  , int
  , cw
  , rat

    -- * Coenumeration combinators
  , takeC, dropC, modulo, postcompose, overlayC
  , infinite
  , (><), (<+>)
  , maybeOf, eitherOf, listOf, finiteSubsetOf

    -- * Utilities
  , unList, unSet
  ) where

import Control.Applicative(Alternative(empty))
import Data.Void
import Data.Bits
import Data.List (foldl')
import Data.Ratio

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible(lost, Divisible(..), Decidable(..))

import Data.Enumeration (Index, Cardinality(..), isFinite)
import qualified Data.Enumeration as E
import Data.Enumeration.Invertible (undiagonal)

data CoEnumeration a = CoEnumeration
  { card :: Cardinality
  , locate :: a -> Index
  }

unsafeMkCoEnumeration :: Cardinality -> (a -> Index) -> CoEnumeration a
unsafeMkCoEnumeration = CoEnumeration

instance Contravariant CoEnumeration where
  contramap f e = e{ locate = locate e . f }

instance Divisible CoEnumeration where
  divide f a b = contramap f $ a >< b
  conquer = unit

instance Decidable CoEnumeration where
  choose f a b = contramap f $ a <+> b
  lose f = contramap f void

unit :: CoEnumeration a
unit = CoEnumeration{ card = 1, locate = const 0 }

void :: CoEnumeration Void
void = CoEnumeration{ card = 0, locate = const (error "locate void") }

(><) :: CoEnumeration a -> CoEnumeration b -> CoEnumeration (a,b)
e1 >< e2 = CoEnumeration{ card = n1 * n2, locate = locatePair }
  where
    n1 = card e1
    n2 = card e2
    locatePair = case (n1, n2) of
      (_,          Finite n2') -> \(a,b) -> locate e1 a * n2' + locate e2 b
      (Finite n1', Infinite)   -> \(a,b) -> locate e1 a + locate e2 b * n1'
      (Infinite,   Infinite)   -> \(a,b) -> undiagonal (locate e1 a, locate e2 b)

(<+>) :: CoEnumeration a -> CoEnumeration b -> CoEnumeration (Either a b)
e1 <+> e2 = CoEnumeration{ card = n1 + n2, locate = locateEither }
  where
    n1 = card e1
    n2 = card e2
    locateEither = case (n1, n2) of
      (Finite n1', _)          -> either (locate e1) ((n1' +) . locate e2)
      (Infinite,   Finite n2') -> either ((n2' +) . locate e1) (locate e2)
      (Infinite,   Infinite)   -> either ((*2) . locate e1) (succ . (*2) . locate e2)

boundedEnum :: forall a. (Enum a, Bounded a) => CoEnumeration a
boundedEnum = CoEnumeration{ card = size, locate = loc }
  where loc = toInteger . fromEnum
        size = Finite $ 1 + loc (maxBound @a) - loc (minBound @a)

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

infinite :: CoEnumeration a -> CoEnumeration a
infinite e = e{ card = Infinite }

dropC :: Integer -> CoEnumeration a -> CoEnumeration a
dropC k e
  | k == 0      = e
  | card e == 0 = e
  | card e <= Finite k = error "Impossible empty coenumeration"
  | otherwise = CoEnumeration{ card = size, locate = loc }
  where
    size = card e - Finite k
    loc = max 0 . subtract k . locate e

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

modulo :: Integer -> CoEnumeration Integer
modulo n
  | n <= 0    = error $ "modulo: invalid argument " ++ show n
  | otherwise = CoEnumeration{ card = Finite n, locate = (`mod` n) }

postcompose :: CoEnumeration a -> CoEnumeration Integer -> CoEnumeration a
postcompose e f = CoEnumeration{
    card = card f
  , locate = locate f . locate e
  }

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

maybeOf :: CoEnumeration a -> CoEnumeration (Maybe a)
maybeOf e = contramap (maybe (Left ()) Right) $ unit <+> e

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

-- | Given a coenumeration of @a@, make a coenumeration of finite sets of
--   @a@, by ignoring order and repetition from @[a]@.
finiteSubsetOf :: CoEnumeration a -> CoEnumeration [a]
finiteSubsetOf e = CoEnumeration{ card = size, locate = unSet . fmap (locate e) }
  where
    size = case card e of
      Finite k -> Finite (2 ^ k)
      Infinite -> Infinite

unSet :: [Index] -> Index
unSet = foldl' (\n i -> n .|. bit (fromInteger i)) 0

-- TODO: finiteEnumerationOf

