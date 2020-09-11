{-# LANGUAGE ViewPatterns #-}
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
-- Through documentations of this module, these alias of imports are used:
--
-- > import qualified Data.Enumeration as E
-- > import qualified Data.CoEnumeration as C

-----------------------------------------------------------------------------

module Data.ProEnumeration(
    ProEnumeration()
  , card, select, locate, isFinite
  , baseEnum, baseCoEnum, run
  , enumerateRange

  , unsafeMkProEnumeration
  , mkProEnumeration
  
  , Cardinality(..), Index

  , unit, empty
  , singleton
  , modulo, clamped, boundsChecked
  , finiteList, finiteCycle
  , boundedEnum
  , nat, int, cw, rat

  , infinite
  , compose
  , (><), (<+>)
  , maybeOf, eitherOf
  , listOf, finiteSubsetOf

  , enumerateP, coenumerateP
  , proenumerationOf
  , finiteFunctionOf
) where

import qualified Control.Applicative as Ap(Alternative(empty))
import Data.Void

import Data.Functor.Contravariant

import Data.Enumeration (Index, Cardinality(..), Enumeration)
import qualified Data.Enumeration as E
import Data.CoEnumeration (CoEnumeration)
import qualified Data.CoEnumeration as C

-- | A /proenumeration/ is a pair of 'CoEnumeration' and 'Enumeration' 
-- sharing the same cardinality. 
-- Alternatively, a /proenumeration/ can be seen as a function with
-- explicitly enumerated range.
--
-- Through this documentation,
-- proenumerations are shown in diagrams of the following shape:
--
-- >    f      g
-- > a ---> N ---> b  :: ProEnumeration a b
-- 
-- Which means it is a value of @p :: ProEnumeration a b@, with
-- cardinality @N@, @locate p = f@, and @select p = g@.
-- 
-- Seeing @N@ in the diagram as a subset of integers:
-- 
-- > N = {i :: Integer | i < N}
-- 
-- Then it is actually a (category-theoretic)
-- diagram showing values of @ProEnumeration a b@.
data ProEnumeration a b =
  ProEnumeration {
    -- | Get the cardinality of a proenumeration
    card :: Cardinality

    -- | See @E.'E.select'@
  , select :: Index -> b

    -- | See @C.'C.locate'@
  , locate :: a -> Index
  }
  deriving (Functor)

-- | Returns if the the cardinality of a proenumeration is finite.
isFinite :: ProEnumeration a b -> Bool
isFinite = (/= Infinite) . card

-- | ProEnumeration is Profunctor
--
-- > dimap l r p = l .@ p @. r
dimap :: (a' -> a) -> (b -> b') -> ProEnumeration a b -> ProEnumeration a' b'
dimap l r p = p{ select = r . select p, locate = locate p . l }

-- | > p @. r = dimap id r p
(@.) :: ProEnumeration a b -> (b -> b') -> ProEnumeration a b'
(@.) = flip fmap

infixl 7 @.

-- | > l .@ p = dimap l id p
(.@) :: (a' -> a) -> ProEnumeration a b -> ProEnumeration a' b
l .@ p = p{ locate = locate p . l }

infixr 8 .@

-- | Take an 'Enumeration' from a proenumeration,
--   discarding @CoEnumeration@ part
baseEnum :: ProEnumeration a b -> Enumeration b
baseEnum p = E.mkEnumeration (card p) (select p)

-- | Take an 'CoEnumeration' from a proenumeration,
--   discarding @Enumeration@ part
baseCoEnum :: ProEnumeration a b -> CoEnumeration a
baseCoEnum p = C.unsafeMkCoEnumeration (card p) (locate p)

-- | Turn a proenumeration into normal function.
--
-- > run p = (select p :: Index -> b) . (locate p :: a -> Index)
run :: ProEnumeration a b -> a -> b
run p = select p . locate p

-- * Primitive proenumerations

-- | @enumerateRange = E.enumerate . 'baseEnum'@
enumerateRange :: ProEnumeration a b -> [b]
enumerateRange = E.enumerate . baseEnum

-- | Constructs a proenumeration from a 'CoEnumeration' and an 'Enumeration'.
--
--   Cardinalities of two arguments must be equal to another.
--   Otherwise, 'mkProEnumeration' returns an error.
--
--   > baseEnum (mkProEnumeration a b) = b
--   > baseCoEnum (mkProEnumeration a b) = a
--
-- >>> p = mkProEnumeration (C.modulo 3) (E.finiteList "abc")
-- >>> (card p, locate p 4, select p 1)
-- (Finite 3,1,'b')
mkProEnumeration :: CoEnumeration a -> Enumeration b -> ProEnumeration a b
mkProEnumeration a b
  | na == nb  = p
  | otherwise = error $ "mkProEnumeration cardinality mismatch:" ++ show (na, nb)
  where
    na = C.card a
    nb = E.card b
    p = ProEnumeration{ card = na, select = E.select b, locate = C.locate a }

-- | Constructs a proenumeration.
--
--   To construct valid proenumeration by @unsafeMkProEnumeration n f g@,
--   it must satisfy the following conditions:
--
--   * For all @i :: Integer@, if @0 <= i && i < n@, then @f i@ should be
--     \"valid\" (usually, it means @f i@ should evaluate without exception).
--   * For all @x :: a@, @(Finite (g x) < n)@.
--   
--   This functions does not (and never could) check the validity
--   of its arguments.
unsafeMkProEnumeration
  :: Cardinality-> (Index -> b) -> (a -> Index) -> ProEnumeration a b
unsafeMkProEnumeration = ProEnumeration

-- | @unit = 'mkProEnumeration' C.'C.unit' E.'E.unit'@
unit :: ProEnumeration a ()
unit = mkProEnumeration C.unit E.unit

-- | @singleton b = b <$ 'unit' = 'mkProEnumeration' C.'C.unit' (E.'E.singleton' b)@
singleton :: b -> ProEnumeration a b
singleton b = mkProEnumeration C.unit (E.singleton b)

-- | @empty = 'mkProEnumeration' 'lost' 'Ap.empty'@
empty :: ProEnumeration Void b
empty = mkProEnumeration C.lost Ap.empty

-- | @boundedEnum = 'mkProEnumeration' C.'C.boundedEnum' E.'E.boundedEnum'@
boundedEnum :: (Enum a, Bounded a) => ProEnumeration a a
boundedEnum = mkProEnumeration C.boundedEnum E.boundedEnum

-- | @modulo k = 'mkProEnumeration' (C.'C.modulo' k) (E.'E.finite' k)@
--
-- >>> card (modulo 13) == Finite 13
-- True
-- >>> run (modulo 13) 1462325 == 1462325 `mod` 13
-- True
modulo :: Integer -> ProEnumeration Integer Integer
modulo k = mkProEnumeration (C.modulo k) (E.finite k)

-- | @clamped lo hi@ is a proenumeration of integers,
--   which does not modify integers between @lo@ and @hi@, inclusive,
--   and limits smaller (larger) integer to @lo@ (@hi@).
--
--   It is error to call this function if @lo > hi@.
--
--   > run (clamped lo hi) = min hi . max lo
--
-- >>> card (clamped (-2) 2)
-- Finite 5
-- >>> enumerateRange (clamped (-2) 2)
-- [-2,-1,0,1,2]
-- >>> run (clamped (-2) 2) <$> [-4 .. 4]
-- [-2,-2,-2,-1,0,1,2,2,2]
clamped :: Integer -> Integer -> ProEnumeration Integer Integer
clamped lo hi
  | lo <= hi = ProEnumeration
      { card = Finite (1 + hi - lo)
      , select = (+ lo)
      , locate = \i -> min (hi - lo) (max 0 (i - lo))
      }
  | otherwise = error "Empty range"

-- | @boundsChecked lo hi@ is a proenumeration of \"bounds check\" function,
--   which validates an input is between @lo@ and @hi@, inclusive,
--   and returns @Nothing@ if it is outside that bounds.
--
--   > run (boundsChecked lo hi) i
--       | lo <= i && i <= hi = Just i
--       | otherwise          = Nothing
--
-- >>> card (boundsChecked (-2) 2)
-- Finite 6
-- >>> -- Justs of [-2 .. 2] and Nothing
-- >>> enumerateRange (boundsChecked (-2) 2)
-- [Just (-2),Just (-1),Just 0,Just 1,Just 2,Nothing]
-- >>> run (boundsChecked (-2) 2) <$> [-4 .. 4]
-- [Nothing,Nothing,Just (-2),Just (-1),Just 0,Just 1,Just 2,Nothing,Nothing]
boundsChecked :: Integer -> Integer -> ProEnumeration Integer (Maybe Integer)
boundsChecked lo hi = ProEnumeration
  { card = Finite size
  , select = sel
  , locate = loc
  }
  where
    n = 1 + hi - lo
    size = 1 + max 0 n
    sel i
      | 0 <= i && i < n = Just (i + lo)
      | i == n          = Nothing
      | otherwise = error "out of bounds"
    loc k | lo <= k && k <= hi = k - lo
          | otherwise          = n


-- | @finiteList as@ is a proenumeration of \"bounds checked\"
--   indexing of @as@.
--   
--   > run (finiteList as) i
--       | 0 <= i && i < length as = Just (as !! i)
--       | otherwise               = Nothing
--
--   Note that 'finiteList' uses '!!' on the input list
--   under the hood, which have bad performance for longer list.
--   See the documentation of Data.Enumeration.'E.finiteList' too.
-- >>> card (finiteList "HELLO")
-- Finite 6
-- >>> -- Justs and Nothing
-- >>> enumerateRange (finiteList "HELLO")
-- [Just 'H',Just 'E',Just 'L',Just 'L',Just 'O',Nothing]
-- >>> run (finiteList "HELLO") <$> [0 .. 6]
-- [Just 'H',Just 'E',Just 'L',Just 'L',Just 'O',Nothing,Nothing]
finiteList :: [a] -> ProEnumeration Integer (Maybe a)
finiteList as = boundsChecked 0 (n-1) @. (fmap sel)
  where
    as' = E.finiteList as
    Finite n = E.card as'
    sel = E.select as'

-- | @finiteCycle as@ is a proenumeration of indexing of @as@,
--   where every integer is valid index by taking modulo @length as@.
--   
--   > run (finiteCycle as) i = as !! (i `mod` length as)
--
--   If @as@ is an empty list, it is an error.
--
-- >>> card (finiteCycle "HELLO")
-- Finite 5
-- >>> enumerateRange (finiteCycle "HELLO")
-- "HELLO"
-- >>> run (finiteCycle "HELLO") <$> [0 .. 10]
-- "HELLOHELLOH"
finiteCycle :: [a] -> ProEnumeration Integer a
finiteCycle as = modulo n @. sel
  where
    as' = E.finiteList as
    Finite n = E.card as'
    sel = E.select as'

-- | @nat = 'mkProEnumeration' C.'C.nat' E.'E.nat'@
nat :: ProEnumeration Integer Integer
nat = mkProEnumeration C.nat E.nat

-- | @int = 'mkProEnumeration' C.'C.int' E.'E.int'@
int :: ProEnumeration Integer Integer
int = mkProEnumeration C.int E.int

-- | @cw = 'mkProEnumeration' C.'C.cw' E.'E.cw'@
cw :: ProEnumeration Rational Rational
cw = mkProEnumeration C.cw E.cw

-- | @rat = 'mkProEnumeration' C.'C.rat' E.'E.rat'@
rat :: ProEnumeration Rational Rational
rat = mkProEnumeration C.rat E.rat

-- | Sets the cardinality of given proenumeration to 'Infinite'
infinite :: ProEnumeration a b -> ProEnumeration a b
infinite p = p{ card = Infinite }

-- * Proenumeration combinators

-- | From two proenumerations @p, q@, makes a proenumeration
--   @compose p q@ which behaves as a composed function
--   (in diagrammatic order like 'Control.Category.>>>'.)
--
--   > run (compose p q) = run q . run p
--   
--   @p@ and @q@ can be drawn in a diagram, like the following:
--   
--   > [_______p______] [______q______]
--   > 
--   >    lp      sp      lq      sq
--   > a ----> N ----> b ----> M ----> c
--   
--   To get a proenumeration @a -> ?? -> c@, there are two obvious choices:
--
--   >       run p >>> lq         sq
--   > a --------------------> M ----> c
--   >    lp         sp >>> run q
--   > a ----> N --------------------> c
--   
--   This function choose one with smaller cardinality between above two.
compose :: ProEnumeration a b -> ProEnumeration b c -> ProEnumeration a c
compose p q
  | card p <= card q = p @. run q
  | otherwise        = run p .@ q

-- | Cartesian product of proenumerations.
-- 
-- @
-- p >< q = 'mkProEnumeration' (baseCoEnum p C.'C.><' baseCoEnum q)
--                             (baseEnum p   E.'E.><' baseEnum q)
-- @
-- 
-- This operation is not associative if and only if one of arguments
-- is not finite.
(><) :: ProEnumeration a1 b1 -> ProEnumeration a2 b2 -> ProEnumeration (a1,a2) (b1,b2)
p >< q = mkProEnumeration (baseCoEnum p C.>< baseCoEnum q) (baseEnum p E.>< baseEnum q)

-- | Direct product of proenumerations.
-- 
-- @
-- p <+> q = 'mkProEnumeration'
--    (baseCoEnum p C.'C.<+>'        baseCoEnum q)
--    (baseEnum p   `E.'E.eitherOf'` baseEnum q)
-- @
-- This operation is not associative if and only if one of arguments
-- is not finite.
(<+>) :: ProEnumeration a1 b1 -> ProEnumeration a2 b2
      -> ProEnumeration (Either a1 a2) (Either b1 b2)
p <+> q = mkProEnumeration (baseCoEnum p C.<+> baseCoEnum q) (E.eitherOf (baseEnum p) (baseEnum q))

-- | @maybeOf p = 'mkProEnumeration' (C.'C.maybeOf' (baseCoEnum p)) (E.'E.maybeOf' (baseEnum p))@
maybeOf :: ProEnumeration a b -> ProEnumeration (Maybe a) (Maybe b)
maybeOf p = dimap (maybe (Left ()) Right) (either (const Nothing) Just) $
              unit <+> p

-- | Synonym of '(<+>)'
eitherOf :: ProEnumeration a1 b1 -> ProEnumeration a2 b2
         -> ProEnumeration (Either a1 a2) (Either b1 b2)
eitherOf = (<+>)

-- | @listOf p = 'mkProEnumeration' (C.'C.listOf' (baseCoEnum p)) (E.'E.listOf' (baseEnum p))@
listOf :: ProEnumeration a b -> ProEnumeration [a] [b]
listOf p = mkProEnumeration (C.listOf (baseCoEnum p)) (E.listOf (baseEnum p))

-- |
-- @
-- finiteSubsetOf p = 'mkProEnumeration'
--     (C.'C.finiteSubsetOf' (baseCoEnum p))
--     (E.'E.finiteSubsetOf' (baseEnum p))
-- @
finiteSubsetOf :: ProEnumeration a b -> ProEnumeration [a] [b]
finiteSubsetOf p =
  mkProEnumeration (C.finiteSubsetOf (baseCoEnum p)) (E.finiteSubsetOf (baseEnum p))

-- | Enumerate every possible proenumerations.
--
-- For @enumerateP a b@, it generates proenumerations @p@
-- such that the function @run p@ have the following properties:
-- 
-- * Range of @run p@ is a subset of @b :: Enumeration b@.
-- * If @locate a x = locate a y@, then @run p x = run p y@.
--   In other words, @run p@ factor through @locate a@.
-- 
-- This function generates @p@ so every function of type @a -> b@ with above
-- properties uniquely appears as @run p@.
enumerateP :: CoEnumeration a -> Enumeration b -> Enumeration (ProEnumeration a b)
enumerateP a b = case (C.card a, E.card b) of
  (0, _) -> E.singleton (mkProEnumeration a Ap.empty)
  (_, 1) -> E.singleton (mkProEnumeration C.unit b)
  (Finite k,_) -> mkProEnumeration a <$> E.finiteEnumerationOf (fromInteger k) b
  (Infinite,_) -> error "infinite domain"

-- | Coenumerate every possible functions.
--
-- For @coenumerateP as bs@, it classifies functions of type @a -> b@
-- by the following criteria:
-- 
--     @f@ and @g@ have the same index ⇔  
--     For all elements @a@ of @as :: Enumeration a@,
--     @locate bs (f a) = locate bs (g a)@.
-- 
-- /Note/: The suffix @P@ suggests it coenumerates @ProEnumeration a b@,
-- but it actually coenumerates @a -> b@. It has a reason.
-- 
-- @ProEnumeration a b@ carries extra data and constraints like its cardinality,
-- but classification does not care those. Thus, it is more allowing to
-- accept any function of type @a -> b@.
-- 
-- To force it coenumerate proenumerations,
-- @'contramap' 'run'@ can be applied.
coenumerateP :: Enumeration a -> CoEnumeration b -> CoEnumeration (a -> b)
coenumerateP a b = case (E.card a, C.card b) of
  (0, _) -> C.unit
  (_, 1) -> C.unit
  (Finite k,_) -> contramap (\f -> f . E.select a) $ C.finiteFunctionOf k b
  (Infinite,_) -> error "infinite domain"

{- | 'enumerateP' and 'coenumerateP' combined.

>    l_a      s_a
> a -----> N -----> a'  :: ProEnumeration a a'
>
>    l_b      s_b
> b -----> M -----> b'  :: ProEnumeration b b'
> 
> 
> (N -> b) ---> (N -> M) ---> (N -> b')
>    ^             ||             |
>    | (. s_a)     ||             | (. l_a)
>    |             ||             v
> (a' -> b)      (M ^ N)       (a -> b')

* When @N@ is finite, @(M ^ N)@ is at most countable, since @M@ is
  at most countable.

* The enumerated functions (of type @a -> b'@) are compositions
  of @l_a :: a -> N@ and functions of type @N -> b@.
  It is beneficial to tell this fact by the type,
  which happens to be @ProEnumeration a b'@.

-}
proenumerationOf
  :: ProEnumeration a a'
  -> ProEnumeration b b'
  -> ProEnumeration (a' -> b) (ProEnumeration a b')
proenumerationOf a b
  = mkProEnumeration
      (coenumerateP (baseEnum a) (baseCoEnum b))
      (enumerateP (baseCoEnum a) (baseEnum b))

-- | @finiteFunctionOf k p@ is a proenumeration of products of @k@ copies of
--   @a@, @b@ respectively.
--
--   If @p@ is a invertible enumeration, @finiteFunctionOf k p@ is too.
--
--   It is implemented using 'proenumerationOf'.
finiteFunctionOf
  :: Integer -> ProEnumeration a b -> ProEnumeration (Integer -> a) (Integer -> b)
finiteFunctionOf k p = proenumerationOf (modulo k) p @. select
