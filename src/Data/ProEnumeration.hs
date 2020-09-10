{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- SPDX-License-Identifier: BSD-3-Clause

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.ProEnumeration
-- Copyright   :  Brent Yorgey, Koji Miyazato
-- Maintainer  :  byorgey@gmail.com
-- 
-- A /proenumeration/ is a pair of 'CoEnumeration' and 'Enumeration' 
-- sharing the same cardinality.
-- 
-- A /proenumeration/ can be seen as a function with explicitly enumerated
-- range.
-- 
-- TODO examples

-----------------------------------------------------------------------------

module Data.ProEnumeration(
    ProEnumeration()
  , card, select, locate
  
  , Cardinality(..), Index, isFinite

  , unit, empty
  , singleton
  , modulo
  , clamped
  , boundedEnum
  , nat
  , int
  , 
) where

import qualified Control.Applicative as Ap(Alternative(empty))
import Data.Void
import Data.Bits
import Data.List (foldl')
import Data.Ratio

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible(Divisible(..), Decidable(..))

import Data.Enumeration (Index, Cardinality(..), Enumeration)
import qualified Data.Enumeration as E
import Data.CoEnumeration (CoEnumeration)
import qualified Data.CoEnumeration as C
import Data.Enumeration.Invertible (undiagonal)

data ProEnumeration a b =
  ProEnumeration {
    card :: Cardinality
  , select :: Index -> b
  , locate :: a -> Index
  }
  deriving (Functor)

isFinite :: ProEnumeration a b -> Bool
isFinite = (/= Infinite) . card

-- | ProEnumeration is Profunctor
--
-- > dimap l r p = l .@ p @. r
dimap :: (a' -> a) -> (b -> b') -> ProEnumeration a b -> ProEnumeration a' b'
dimap l r p = p{ select = r . select p, locate = locate p . l }

(@.) :: ProEnumeration a b -> (b -> b') -> ProEnumeration a b'
(@.) = flip fmap

infixl 7 @.

(.@) :: (a' -> a) -> ProEnumeration a b -> ProEnumeration a' b
l .@ p = p{ locate = locate p . l }

infixr 8 .@

baseEnum :: ProEnumeration a b -> Enumeration b
baseEnum p = E.mkEnumeration (card p) (select p)

baseCoEnum :: ProEnumeration a b -> CoEnumeration a
baseCoEnum p = C.unsafeMkCoEnumeration (card p) (locate p)

-- | Turn a proenumeration into normal function
run :: ProEnumeration a b -> a -> b
run p = select p . locate p

-- * Primitive proenumerations

enumerateRange :: ProEnumeration a b -> [b]
enumerateRange = E.enumerate . baseEnum

unsafeMkProEnumeration
  :: Cardinality-> (Index -> b) -> (a -> Index) -> ProEnumeration a b
unsafeMkProEnumeration = ProEnumeration

combine_ :: CoEnumeration a -> Enumeration b -> ProEnumeration a b
combine_ a b
  | na == nb  = p
  | otherwise = error $ "combine_ cardinality mismatch:" ++ show (na, nb)
  where
    na = C.card a
    nb = E.card b
    p = ProEnumeration{
        card = na
      , select = E.select b
      , locate = C.locate a
      }

unit :: ProEnumeration a ()
unit = combine_ C.unit E.unit

singleton :: b -> ProEnumeration a b
-- singleton b = dimap id (const b) unit
singleton b = combine_ C.unit (E.singleton b)

empty :: ProEnumeration Void b
empty = combine_ C.lost Ap.empty

boundedEnum :: (Enum a, Bounded a) => ProEnumeration a a
boundedEnum = combine_ C.boundedEnum E.boundedEnum

modulo :: Integer -> ProEnumeration Integer Integer
modulo k = combine_ (C.modulo k) (E.finite k)

clamped :: Integer -> Integer -> ProEnumeration Integer Integer
clamped lo hi
  | lo <= hi = ProEnumeration
      { card = Finite (1 + hi - lo)
      , select = (+ lo)
      , locate = \i -> min (hi - lo) (max 0 (i - lo))
      }
  | otherwise = error "Empty range"

nat :: ProEnumeration Integer Integer
nat = combine_ C.nat E.nat

int :: ProEnumeration Integer Integer
int = combine_ C.int E.int

cw :: ProEnumeration Rational Rational
cw = combine_ C.cw E.cw

rat :: ProEnumeration Rational Rational
rat = combine_ C.rat E.rat

infinite :: ProEnumeration a b -> ProEnumeration a b
infinite p = p{ card = Infinite }

-- * Proenumeration combinators

compose :: ProEnumeration a b -> ProEnumeration b c -> ProEnumeration a c
compose p q
  | card p <= card q = p @. run q
  | otherwise        = run p .@ q

(><) :: ProEnumeration a1 b1 -> ProEnumeration a2 b2 -> ProEnumeration (a1,a2) (b1,b2)
p >< q = combine_ (baseCoEnum p C.>< baseCoEnum q) (baseEnum p E.>< baseEnum q)

(<+>) :: ProEnumeration a1 b1 -> ProEnumeration a2 b2
      -> ProEnumeration (Either a1 a2) (Either b1 b2)
p <+> q = combine_ (baseCoEnum p C.<+> baseCoEnum q) (E.eitherOf (baseEnum p) (baseEnum q))

listOf :: ProEnumeration a b -> ProEnumeration [a] [b]
listOf p = combine_ (C.listOf (baseCoEnum p)) (E.listOf (baseEnum p))

finiteSubsetOf :: ProEnumeration a b -> ProEnumeration [a] [b]
finiteSubsetOf p =
  combine_ (C.finiteSubsetOf (baseCoEnum p)) (E.finiteSubsetOf (baseEnum p))

enumerateP :: CoEnumeration a -> Enumeration b -> Enumeration (ProEnumeration a b)
enumerateP a b = case (C.card a, E.card b) of
  (0, _) -> E.singleton (combine_ a Ap.empty)
  (_, 1) -> E.singleton (combine_ C.unit b)
  (Finite k,_) -> combine_ a <$> E.finiteEnumerationOf (fromInteger k) b
  (Infinite,_) -> error "infinite domain"

coenumerateP :: Enumeration a -> CoEnumeration b -> CoEnumeration (ProEnumeration a b)
coenumerateP a b = case (E.card a, C.card b) of
  (0, _) -> C.unit
  (_, 1) -> C.unit
  (Finite k,_) -> contramap (\p -> run p . E.select a) $ C.finiteFunctionOf k b
  (Infinite,_) -> error "infinite domain"

{- |

>    l_a      s_a
> a -----> N -----> a'
>    l_b      s_b
> b -----> M -----> b'
> 
> s_a = select a
> l_a = locate a
>     :
>     etc.
> 
> When N is finite:
> 
> (N -> b) -> M^N -> (N -> b')
>    ^                  |
>    | (∘ s_a)          | (∘ l_a)
>    |                  v
> (a' -> b)          (a -> b')

-}
proenumerationOf
  :: ProEnumeration a a'
  -> ProEnumeration b b'
  -> ProEnumeration (ProEnumeration a' b) (ProEnumeration a b')
proenumerationOf a b
  = combine_ (coenumerateP (baseEnum a) (baseCoEnum b))
             (enumerateP (baseCoEnum a) (baseEnum b))

finiteFunctionOf
  :: Integer -> ProEnumeration a b -> ProEnumeration (Integer -> a) (Integer -> b)
finiteFunctionOf k p = dimap l r $ proenumerationOf (modulo k) p
  where
    l f = modulo k @. f
    r = select
