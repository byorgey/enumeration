{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE DeriveFunctor #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Enumeration
-- Copyright   :  Brent Yorgey
-- Maintainer  :  byorgey@gmail.com
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- An /enumeration/ is a finite or countably infinite sequence of
-- values, represented as a function from an index to a value, so it
-- works even for very large finite sets and supports random uniform
-- sampling.
--
-- Enumerations are isomorphic to lists, so some functions in this
-- module have the same name as common list functions.  It is
-- recommended to import this module qualified, e.g. XXX
--
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase    #-}

module Data.Enumeration
  ( -- * Enumerations

    Cardinality(..), Index
  , Enumeration, card, select

    -- ** Constructing

  , void
  , unit
  , singleton
  , always
  , finite
  , finiteList
  , infinite
  , drop

  , nat
  , cw

  , interleave
  , (><)
  , (+++)

  , zip, zipWith

    -- ** Using

  , isFinite
  , enumerate

    -- * Utilities

  , diagonal

  ) where

import           Prelude             hiding (drop, zip, zipWith)
import qualified Prelude             as P

import           Control.Applicative

import           Data.Ratio
import           Data.Tuple          (swap)

------------------------------------------------------------
-- Enumerations
------------------------------------------------------------

-- | The cardinality of a countable set: either a specific finite
--   natural number, or countably infinite.
data Cardinality = Finite !Integer | Infinite
  deriving (Show, Eq, Ord)

-- | @Cardinality@ has a @Num@ instance for convenience, so we can use
--   numeric literals as finite cardinalities, and add, subtract, and
--   multiply cardinalities.  Note that:
--
--   * subtraction is saturating (/i.e./ 3 - 5 = 0)
--
--   * infinity - infinity is treated as zero
--
--   * zero is treated as a "very strong" annihilator for multiplication:
--     even infinity * zero = zero.
instance Num Cardinality where
  fromInteger = Finite

  Infinite + _        = Infinite
  _        + Infinite = Infinite
  Finite a + Finite b = Finite (a + b)

  Finite 0 * _        = Finite 0
  _        * Finite 0 = Finite 0
  Infinite * _        = Infinite
  _        * Infinite = Infinite
  Finite a * Finite b = Finite (a * b)

  Finite a - Finite b = Finite (max 0 (a - b))
  _        - Infinite = Finite 0
  _        - _        = Infinite

  negate = error "Can't negate Cardinality"
  signum = error "No signum for Cardinality"
  abs    = error "No abs for Cardinality"

-- | An index into an enumeration.
type Index = Integer

-- | A basic enumeration of a finite or countably infinite set of
--   values. XXX
--
--   'Enumeration' is an instance of the following type classes:
--
--   * 'Functor' (you can map a function over every element of an enumeration)
--   * 'Applicative' (Cartesian product of enumerations)
--   * 'Alternative' (disjoint union of enumerations)
--
--   'Enumeration' is /not/ a 'Monad', since XXX
data Enumeration a = Enumeration
  { -- | Get the cardinality of an enumeration.
    card   :: Cardinality

    -- | Select the value at a particular index of an enumeration.
    --   Precondition: the index must be strictly less than the
    --   cardinality.  For infinite sets, every possible value must
    --   occur at some finite index.
  , select :: Index -> a
  }
  deriving Functor

-- | The @Applicative@ instance for @Enumeration@ works similarly to
--   the instance for lists:
--
--   * @pure = always@
--
--   * @f '<*>' x@ takes the Cartesian product ('><') of @f@ and @x@
--     and applies the function to the argument in each pair.
instance Applicative Enumeration where
  pure    = always
  f <*> x = uncurry ($) <$> (f >< x)

-- | The @Alternative@ instance for @Enumeration@ represents disjoint
--   union of enumerations.
instance Alternative Enumeration where

  -- | The empty ('void') enumeration.
  empty = void

  -- | Disjoint union of enumerations; see '+++'.  Note that this is
  --   not associative in a strict sense.  However, it is associative
  --   if enumerations are considered equivalent up to reordering.
  (<|>) = (+++)

-- XXX Enumeration can't be Monad given the way +++ needs to know
-- whether its arguments are finite or infinite?

-- | Test whether an enumeration is finite.
--
-- >>> isFinite (finiteList [1,2,3])
-- True
--
-- >>> isFinite nat
-- False
isFinite :: Enumeration a -> Bool
isFinite (Enumeration (Finite _) _) = True
isFinite _                          = False

------------------------------------------------------------
-- Constructing Enumerations
------------------------------------------------------------

-- | XXX
finite :: Integer -> Enumeration Integer
finite n = Enumeration (Finite n) id

-- | Construct an enumeration from the elements of a finite list,
--   which are assumed to be distinct.  To turn an enumeration back
--   into a list, use 'enumerate'.
--
--   Note 'finiteList' will "work" on an infinite list, but only if
--   one never inspects the cardinality of the resulting enumeration;
--   evaluating the cardinality will cause it to hang trying to
--   compute the length of an infinite list.  To make an infinite
--   enumeration, use something like @f <$> 'nat'@ where @f@ is a
--   function to compute the value at any given index.
finiteList :: [a] -> Enumeration a
finiteList as = Enumeration (Finite (fromIntegral $ length as)) (\k -> as !! fromIntegral k)
  -- Note the use of !! is not very efficient, but for small lists it
  -- probably still beats the overhead of allocating a vector.  Most
  -- likely this will only ever be used with very small lists anyway.
  -- If it becomes a problem we could add another combinator that
  -- behaves just like finiteList but allocates a Vector internally.



-- data Tree = Leaf | Branch Tree Tree
--
-- tree :: Enumeration Tree
-- tree = infinite $ (Leaf <$ unit) <|> (Branch <$> tree <*> tree)
--
-- take 10 $ enumerate tree
--
-- select tree 9873509823957230983046702973027

-- | XXX
infinite :: Enumeration a -> Enumeration a
infinite (Enumeration _ s) = Enumeration Infinite s

-- | List the elememts of an enumeration in order.  Inverse of
--   'finiteList'.
enumerate :: Enumeration a -> [a]
enumerate e = case card e of
  Infinite -> map (select e) [0 ..]
  Finite c -> map (select e) [0 .. c-1]

-- | The empty enumeration, with cardinality zero and no elements.
--
-- >>> enumerate void
-- []
void :: Enumeration a
void = Enumeration 0 (error "select void")

-- | The unit enumeration, with a single value of @()@.
--
-- >>> enumerate unit
-- [()]
unit :: Enumeration ()
unit = Enumeration
  { card = 1
  , select = \case { 0 -> (); i -> error $ "select unit " ++ show i }
  }

-- | An enumeration of a single given element.
--
-- >>> enumerate (singleton 17)
-- [17]
singleton :: a -> Enumeration a
singleton a = Enumeration 1 (const a)

-- | A constant infinite enumeration.
--
-- >>> take 10 . enumerate $ always 17
-- [17,17,17,17,17,17,17,17,17,17]
always :: a -> Enumeration a
always a = Enumeration Infinite (const a)

-- | The natural numbers, @0, 1, 2, ...@.
--
-- >>> take 10 . enumerate $ nat
-- [0,1,2,3,4,5,6,7,8,9]
nat :: Enumeration Integer
nat = Enumeration Infinite id

-- | The positive rational numbers, enumerated according to the
--   [Calkin-Wilf sequence](http://www.cs.ox.ac.uk/publications/publication1664-abstract.html).
--
-- >>> take 10 . enumerate $ cw
-- [1 % 1,1 % 2,2 % 1,1 % 3,3 % 2,2 % 3,3 % 1,1 % 4,4 % 3,3 % 5]
cw :: Enumeration Rational
cw = Enumeration { card = Infinite, select = uncurry (%) . go . succ }
  where
    go 1 = (1,1)
    go n
      | even n    = left (go (n `div` 2))
      | otherwise = right (go (n `div` 2))
    left  (!a, !b) = (a, a+b)
    right (!a, !b) = (a+b, b)

-- XXX use Alternative for +++!  Does it satisfy laws?
infixr 5 +++

-- | Sum, /i.e./ disjoint union, of two enumerations.  If both are
--   finite, all the values of the first will be enumerated before the
--   values of the second.  If only one is finite, the values from the
--   finite set will be listed first.  If both are infinite, a fair
--   (alternating) interleaving is used.
--
-- >>> take 10 . enumerate $ singleton 17 +++ nat
-- [17,0,1,2,3,4,5,6,7,8]
--
-- >>> take 10 . enumerate $ nat +++ singleton 17
-- [17,0,1,2,3,4,5,6,7,8]
--
-- >>> take 10 . enumerate $ nat +++ (negate <$> nat)
-- [0,0,1,-1,2,-2,3,-3,4,-4]
(+++) :: Enumeration a -> Enumeration a -> Enumeration a
e1 +++ e2 = case (card e1, card e2) of

  -- optimize for void +++ e2
  (Finite 0, _)  -> e2

  -- First enumeration is finite: just put it first
  (Finite k1, _) -> Enumeration
    { card   = card e1 + card e2
    , select = \k -> if k < k1 then select e1 k else select e2 (k - k1)
    }

  -- First is infinite but second is finite: put all the second values first
  (_, Finite _) -> e2 +++ e1

  -- Both are infinite: use a fair (alternating) interleaving
  _ -> interleave (Enumeration 2 (\case {0 -> e1; 1 -> e2}))

-- | Drop some elements from the beginning of an enumeration.  @drop
--   k@ has no effect if \(k \leq 0\).  @drop k@ results in the empty
--   enumeration whenever @k@ is greater than or equal to the
--   cardinality of the enumeration.
--
-- >>> enumerate $ drop 2 (finiteList [1..5])
-- [3,4,5]
--
-- >>> enumerate $ drop 0 (finiteList [1..5])
-- [1,2,3,4,5]
--
-- >>> enumerate $ drop 7 (finiteList [1..5])
-- []
drop :: Integer -> Enumeration a -> Enumeration a
drop m e
  | m <= 0            = e
  | Finite m < card e = Enumeration
      { card = card e - Finite m, select = select e . (+m) }
  | otherwise         = void

-- | Fairly interleave a set of infinite enumerations.
--
--   Precondition: 'interleave' must be given a (finite or infinite)
--   enumeration of /infinite/ enumerations.
--
--   For a finite set of infinite enumerations, a round-robin
--   interleaving is used. That is, if we think of an enumeration of
--   enumerations as a 2D matrix read off row-by-row, this corresponds
--   to taking the transpose of a matrix with finitely many infinite
--   rows.  For an infinite set of infinite enumerations, /i.e./ an
--   infinite 2D matrix, the resulting enumeration reads off the
--   matrix by diagonals.
--
-- >>> take 10 . enumerate $ interleave (finiteList [nat, negate <$> nat, (*10) <$> nat])
-- [0,0,0,1,-1,10,2,-2,20,3]
interleave :: Enumeration (Enumeration a) -> Enumeration a
interleave e = case card e of
  Finite n -> Enumeration
    { card   = Infinite
    , select = \k -> let (i,j) = k `divMod` n in select (select e j) i
    }
  Infinite -> Enumeration
    { card   = Infinite
    , select = \k -> let (i,j) = diagonal k in select (select e j) i
    }

-- | XXX
zip :: Enumeration a -> Enumeration b -> Enumeration (a,b)
zip = zipWith (,)

-- | XXX
zipWith :: (a -> b -> c) -> Enumeration a -> Enumeration b -> Enumeration c
zipWith f e1 e2 =
  Enumeration (min (card e1) (card e2)) (\k -> f (select e1 k) (select e2 k))

-- | One half of the isomorphism between \(\mathbb{N}\) and
--   \(\mathbb{N} \times \mathbb{N}\) which enumerates by diagonals: turn a
--   particular natural number index into its position in the 2D grid.
--
--   @
--   0 1 3 6 ...
--   2 4 7
--   5 8
--   9
--   @
diagonal :: Integer -> (Integer, Integer)
diagonal k = (k - t, d - (k - t))
  where
    d = (integerSqrt (1 + 8*k) - 1) `div` 2
    t = d*(d+1) `div` 2

-- | Cartesian product of enumerations. If both are finite, uses a
--   simple lexicographic ordering.  If only one is finite, the
--   resulting enumeration is still in lexicographic order, with the
--   infinite enumeration as the most significant component.
--   For two infinite enumerations, interleaves them by diagonals.
--
-- >>> enumerate $ finiteList [1..3] >< finiteList "abcd"
-- [(1,'a'),(1,'b'),(1,'c'),(1,'d'),(2,'a'),(2,'b'),(2,'c'),(2,'d'),(3,'a'),(3,'b'),(3,'c'),(3,'d')]
--
-- >>> take 10 . enumerate $ finiteList "abc" >< nat
-- [('a',0),('b',0),('c',0),('a',1),('b',1),('c',1),('a',2),('b',2),('c',2),('a',3)]
--
-- >>> take 10 . enumerate $ nat >< finiteList "abc"
-- [(0,'a'),(0,'b'),(0,'c'),(1,'a'),(1,'b'),(1,'c'),(2,'a'),(2,'b'),(2,'c'),(3,'a')]
--
-- >>> take 10 . enumerate $ nat >< nat
-- [(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),(0,3),(1,2),(2,1),(3,0)]
(><) :: Enumeration a -> Enumeration b -> Enumeration (a,b)
e1 >< e2 = case (card e1, card e2) of

  -- The second enumeration is finite: use lexicographic ordering with
  -- the first as the most significant component
  (_, Finite k2) -> Enumeration
    { card   = card e1 * card e2
    , select = \k -> let (i,j) = k `divMod` k2 in (select e1 i, select e2 j)
    }

  -- The first is finite but the second is infinite: lexicographic
  -- with the second as most significant.
  (Finite _, _) -> swap <$> (e2 >< e1)

  -- Both are infinite: enumerate by diagonals
  _ -> Enumeration
    { card = Infinite
    , select = \k -> let (i,j) = diagonal k in (select e1 i, select e2 j)
    }


-- Note: more efficient integerSqrt in arithmoi
-- (Math.NumberTheory.Powers.Squares), but it's a rather heavyweight
-- dependency to pull in just for this.

-- Implementation of `integerSqrt` taken from the Haskell wiki:
-- https://wiki.haskell.org/Generic_number_type#squareRoot
integerSqrt :: Integer -> Integer
integerSqrt 0 = 0
integerSqrt 1 = 1
integerSqrt n =
  let twopows = iterate (^!2) 2
      (lowerRoot, lowerN) =
        last $ takeWhile ((n>=) . snd) $ P.zip (1:twopows) twopows
      newtonStep x = div (x + div n x) 2
      iters = iterate newtonStep (integerSqrt (div n lowerN ) * lowerRoot)
      isRoot r = r^!2 <= n && n < (r+1)^!2
  in  head $ dropWhile (not . isRoot) iters

(^!) :: Num a => a -> Int -> a
(^!) x n = x^n
