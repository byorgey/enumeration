{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- SPDX-License-Identifier: BSD-3-Clause

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Enumeration
-- Copyright   :  Brent Yorgey
-- Maintainer  :  byorgey@gmail.com
--
-- An /enumeration/ is a finite or countably infinite sequence of
-- values, that is, enumerations are isomorphic to lists.  However,
-- enumerations are represented a functions from index to value, so
-- they support efficient indexing and can be constructed for very
-- large finite sets.  A few examples are shown below.
--
-- >>> enumerate . takeE 15 $ listOf nat
-- [[],[0],[0,0],[1],[0,0,0],[1,0],[2],[0,1],[1,0,0],[2,0],[3],[0,0,0,0],[1,1],[2,0,0],[3,0]]
-- >>> select (listOf nat) 986235087203970702008108646
-- [11987363624969,1854392,1613,15,0,2,0]
--
-- @
-- data Tree = L | B Tree Tree deriving Show
--
-- treesUpTo :: Int -> Enumeration Tree
-- treesUpTo 0 = 'singleton' L
-- treesUpTo n = 'singleton' L '<|>' B '<$>' t' '<*>' t'
--   where t' = treesUpTo (n-1)
--
-- trees :: Enumeration Tree
-- trees = 'infinite' $ 'singleton' L '<|>' B '<$>' trees '<*>' trees
-- @
--
-- >>> card (treesUpTo 1)
-- Finite 2
-- >>> card (treesUpTo 10)
-- Finite 14378219780015246281818710879551167697596193767663736497089725524386087657390556152293078723153293423353330879856663164406809615688082297859526620035327291442156498380795040822304677
-- >>> select (treesUpTo 5) 12345
-- B (B L (B (B (B L L) L) (B L L))) (B (B (B L L) L) (B L L))
--
-- >>> card trees
-- Infinite
-- >>> select trees 12345
-- B (B (B (B L (B L L)) L) (B L (B (B L L) L))) (B (B L (B L L)) (B (B L L) (B L (B L L))))
--

-----------------------------------------------------------------------------

module Data.Enumeration
  ( -- * Enumerations

    Enumeration

    -- ** Using enumerations

  , Cardinality(..), card
  , Index, select

  , isFinite
  , enumerate

    -- ** Primitive enumerations

  , unit
  , singleton
  , always
  , finite
  , finiteList
  , boundedEnum

  , nat
  , int
  , cw
  , rat

  -- ** Enumeration combinators

  , takeE
  , dropE
  , infinite
  , zipE, zipWithE
  , (<+>)
  , (><)
  , interleave

  , maybeOf
  , eitherOf
  , listOf

    -- * Utilities

  , diagonal

  ) where

import           Control.Applicative

import           Data.Ratio
import           Data.Tuple          (swap)

------------------------------------------------------------
-- Setup for doctest examples
------------------------------------------------------------

-- $setup
-- >>> :set -XTypeApplications
-- >>> :{
--   data Tree = L | B Tree Tree deriving Show
--   treesUpTo :: Int -> Enumeration Tree
--   treesUpTo 0 = singleton L
--   treesUpTo n = singleton L <|> B <$> t' <*> t'
--     where t' = treesUpTo (n-1)
--   trees :: Enumeration Tree
--   trees = infinite $ singleton L <|> B <$> trees <*> trees
-- :}

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

-- | An enumeration of a finite or countably infinite set of
--   values. An enumeration is represented as a function from the natural numbers
--   (for infinite enumerations) or a finite prefix of the natural numbers (for finite ones)
--   to values.  Enumerations can thus easily be constructed for very large sets, and
--   support efficient indexing and random sampling.
--
--   'Enumeration' is an instance of the following type classes:
--
--   * 'Functor' (you can map a function over every element of an enumeration)
--   * 'Applicative' (representing Cartesian product of enumerations; see ('><'))
--   * 'Alternative' (representing disjoint union of enumerations; see ('<+>'))
--
--   'Enumeration' is /not/ a 'Monad', since there is no way to
--   implement 'Control.Monad.join' that works for any combination of
--   finite and infinite enumerations (but see 'interleave').
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
--   the instance for lists: @pure = singleton@, and @f '<*>' x@ takes
--   the Cartesian product of @f@ and @x@ (see ('><')) and applies
--   each paired function and argument.
instance Applicative Enumeration where
  pure    = singleton
  f <*> x = uncurry ($) <$> (f >< x)

-- | The @Alternative@ instance for @Enumeration@ represents the sum
--   monoidal structure on enumerations: @empty@ is the empty
--   enumeration, and @('<|>') = ('<+>')@ is disjoint union.
instance Alternative Enumeration where
  empty = void
  (<|>) = (<+>)

------------------------------------------------------------
-- Using enumerations
------------------------------------------------------------

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

-- | List the elements of an enumeration in order.  Inverse of
--   'finiteList'.
enumerate :: Enumeration a -> [a]
enumerate e = case card e of
  Infinite -> map (select e) [0 ..]
  Finite c -> map (select e) [0 .. c-1]

------------------------------------------------------------
-- Constructing Enumerations
------------------------------------------------------------

-- | The empty enumeration, with cardinality zero and no elements.
--
-- >>> card void
-- Finite 0
--
-- >>> enumerate void
-- []
void :: Enumeration a
void = Enumeration 0 (error "select void")

-- | The unit enumeration, with a single value of @()@.
--
-- >>> card unit
-- Finite 1
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
-- >>> card (singleton 17)
-- Finite 1
--
-- >>> enumerate (singleton 17)
-- [17]
singleton :: a -> Enumeration a
singleton a = Enumeration 1 (const a)

-- | A constant infinite enumeration.
--
-- >>> card (always 17)
-- Infinite
--
-- >>> enumerate . takeE 10 $ always 17
-- [17,17,17,17,17,17,17,17,17,17]
always :: a -> Enumeration a
always a = Enumeration Infinite (const a)

-- | A finite prefix of the natural numbers.
--
-- >>> card (finite 5)
-- Finite 5
-- >>> card (finite 1234567890987654321)
-- Finite 1234567890987654321
--
-- >>> enumerate (finite 5)
-- [0,1,2,3,4]
-- >>> enumerate (finite 0)
-- []
finite :: Integer -> Enumeration Integer
finite n = Enumeration (Finite n) id

-- | Construct an enumeration from the elements of a /finite/ list.  To
--   turn an enumeration back into a list, use 'enumerate'.
--
-- >>> enumerate (finiteList [2,3,8,1])
-- [2,3,8,1]
-- >>> select (finiteList [2,3,8,1]) 2
-- 8
--
--   'finiteList' does not work on infinite lists: inspecting the
--   cardinality of the resulting enumeration (something many of the
--   enumeration combinators need to do) will hang trying to compute
--   the length of the infinite list.  To make an infinite enumeration,
--   use something like @f '<$>' 'nat'@ where @f@ is a function to
--   compute the value at any given index.
--
--   'finiteList' uses ('!!') internally, so you probably want to
--   avoid using it on long lists.  It would be possible to make a
--   version with better indexing performance by allocating a vector
--   internally, but I am too lazy to do it.  If you have a good use
--   case let me know (better yet, submit a pull request).
finiteList :: [a] -> Enumeration a
finiteList as = Enumeration (Finite (fromIntegral $ length as)) (\k -> as !! fromIntegral k)
  -- Note the use of !! is not very efficient, but for small lists it
  -- probably still beats the overhead of allocating a vector.  Most
  -- likely this will only ever be used with very small lists anyway.
  -- If it becomes a problem we could add another combinator that
  -- behaves just like finiteList but allocates a Vector internally.

-- | Enumerate all the values of a bounded 'Enum' instance.
--
-- >>> enumerate (boundedEnum @Bool)
-- [False,True]
--
-- >>> select (boundedEnum @Char) 97
-- 'a'
--
-- >>> card (boundedEnum @Int)
-- Finite 18446744073709551616
-- >>> select (boundedEnum @Int) 0
-- -9223372036854775808
boundedEnum :: forall a. (Enum a, Bounded a) => Enumeration a
boundedEnum = Enumeration
  { card = Finite (hi - lo + 1)
  , select = toEnum . fromIntegral . (+lo)
  }
  where
    lo, hi :: Index
    lo = fromIntegral (fromEnum (minBound @a))
    hi = fromIntegral (fromEnum (maxBound @a))

-- | The natural numbers, @0, 1, 2, ...@.
--
-- >>> enumerate . takeE 10 $ nat
-- [0,1,2,3,4,5,6,7,8,9]
nat :: Enumeration Integer
nat = Enumeration Infinite id

-- | All integers in the order @0, 1, -1, 2, -2, 3, -3, ...@.
int :: Enumeration Integer
int = negate <$> nat <|> dropE 1 nat

-- | The positive rational numbers, enumerated according to the
--   [Calkin-Wilf sequence](http://www.cs.ox.ac.uk/publications/publication1664-abstract.html).
--
-- >>> enumerate . takeE 10 $ cw
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

-- | An enumeration of all rational numbers: 0 first, then each
--   rational in the Calkin-Wilf sequence followed by its negative.
--
-- >>> enumerate . takeE 10 $ rat
-- [0 % 1,1 % 1,(-1) % 1,1 % 2,(-1) % 2,2 % 1,(-2) % 1,1 % 3,(-1) % 3,3 % 2]
rat :: Enumeration Rational
rat = singleton 0 <|> (cw <|> negate <$> cw)

-- | Take a finite prefix from the beginning of an enumeration.  @takeE
--   k e@ always yields the empty enumeration for \(k \leq 0\), and
--   results in @e@ whenever @k@ is greater than or equal to the
--   cardinality of the enumeration.  Otherwise @takeE k e@ has
--   cardinality @k@ and matches @e@ from @0@ to @k-1@.
--
-- >>> enumerate $ takeE 3 (boundedEnum @Int)
-- [-9223372036854775808,-9223372036854775807,-9223372036854775806]
--
-- >>> enumerate $ takeE 2 (finiteList [1..5])
-- [1,2]
--
-- >>> enumerate $ takeE 0 (finiteList [1..5])
-- []
--
-- >>> enumerate $ takeE 7 (finiteList [1..5])
-- [1,2,3,4,5]
takeE :: Integer -> Enumeration a -> Enumeration a
takeE k e
  | k <= 0             = void
  | Finite k >= card e = e
  | otherwise = Enumeration (Finite k) (select e)

-- | Drop some elements from the beginning of an enumeration.  @dropE k
--   e@ yields @e@ unchanged if \(k \leq 0\), and results in the empty
--   enumeration whenever @k@ is greater than or equal to the
--   cardinality of @e@.
--
-- >>> enumerate $ dropE 2 (finiteList [1..5])
-- [3,4,5]
--
-- >>> enumerate $ dropE 0 (finiteList [1..5])
-- [1,2,3,4,5]
--
-- >>> enumerate $ dropE 7 (finiteList [1..5])
-- []
dropE :: Integer -> Enumeration a -> Enumeration a
dropE k e
  | k <= 0             = e
  | Finite k >= card e = void
  | otherwise          = Enumeration
      { card = card e - Finite k, select = select e . (+k) }

-- | Explicitly mark an enumeration as having an infinite cardinality,
--   ignoring the previous cardinality. It is sometimes necessary to
--   use this as a "hint" when constructing a recursive enumeration
--   whose cardinality would otherwise consist of an infinite sum of
--   finite cardinalities.
--
--   For example, consider the following definitions:
--
-- @
-- data Tree = L | B Tree Tree deriving Show
--
-- treesBad :: Enumeration Tree
-- treesBad = singleton L '<|>' B '<$>' treesBad '<*>' treesBad
--
-- trees :: Enumeration Tree
-- trees = infinite $ singleton L '<|>' B '<$>' trees '<*>' trees
-- @
--
--   Trying to use @treeBad@ at all will simply hang, since trying to
--   compute its cardinality leads to infinite recursion.
--
-- @
-- \>>>\ select treesBad 5
-- ^CInterrupted.
-- @
--
--   However, using 'infinite', as in the definition of 'trees',
--   provides the needed laziness:
--
-- >>> card trees
-- Infinite
-- >>> enumerate . takeE 3 $ trees
-- [L,B L L,B L (B L L)]
-- >>> select trees 87239862967296
-- B (B (B (B (B L L) (B (B (B L L) L) L)) (B L (B L (B L L)))) (B (B (B L (B L (B L L))) (B (B L L) (B L L))) (B (B L (B L (B L L))) L))) (B (B L (B (B (B L (B L L)) (B L L)) L)) (B (B (B L (B L L)) L) L))
infinite :: Enumeration a -> Enumeration a
infinite (Enumeration _ s) = Enumeration Infinite s

-- | Fairly interleave a set of /infinite/ enumerations.
--
--   For a finite set of infinite enumerations, a round-robin
--   interleaving is used. That is, if we think of an enumeration of
--   enumerations as a 2D matrix read off row-by-row, this corresponds
--   to taking the transpose of a matrix with finitely many infinite
--   rows, turning it into one with infinitely many finite rows.  For
--   an infinite set of infinite enumerations, /i.e./ an infinite 2D
--   matrix, the resulting enumeration reads off the matrix by
--   'diagonal's.
--
-- >>> enumerate . takeE 15 $ interleave (finiteList [nat, negate <$> nat, (*10) <$> nat])
-- [0,0,0,1,-1,10,2,-2,20,3,-3,30,4,-4,40]
--
-- >>> enumerate . takeE 15 $ interleave (always nat)
-- [0,0,1,0,1,2,0,1,2,3,0,1,2,3,4]
--
--   This function is similar to 'Control.Monad.join' in a
--   hypothetical 'Monad' instance for 'Enumeration', but it only
--   works when the inner enumerations are all infinite.
--
--   To interleave a finite enumeration of enumerations, some of which
--   may be finite, you can use @'Data.Foldable.asum' . 'enumerate'@.
--   If you want to interleave an infinite enumeration of finite
--   enumerations, you are out of luck.
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

-- | Zip two enumerations in parallel, producing the pair of
--   elements at each index.  The resulting enumeration is truncated
--   to the cardinality of the smaller of the two arguments.
--
-- >>> enumerate $ zipE nat (boundedEnum @Bool)
-- [(0,False),(1,True)]
zipE :: Enumeration a -> Enumeration b -> Enumeration (a,b)
zipE = zipWithE (,)

-- | Zip two enumerations in parallel, applying the given function to
--   the pair of elements at each index to produce a new element.  The
--   resulting enumeration is truncated to the cardinality of the
--   smaller of the two arguments.
--
-- >>> enumerate $ zipWithE replicate (finiteList [1..10]) (dropE 35 (boundedEnum @Char))
-- ["#","$$","%%%","&&&&","'''''","((((((",")))))))","********","+++++++++",",,,,,,,,,,"]

zipWithE :: (a -> b -> c) -> Enumeration a -> Enumeration b -> Enumeration c
zipWithE f e1 e2 =
  Enumeration (min (card e1) (card e2)) (\k -> f (select e1 k) (select e2 k))

-- | Sum, /i.e./ disjoint union, of two enumerations.  If both are
--   finite, all the values of the first will be enumerated before the
--   values of the second.  If only one is finite, the values from the
--   finite enumeration will be listed first.  If both are infinite, a
--   fair (alternating) interleaving is used, so that every value ends
--   up at a finite index in the result.
--
--   Note that the ('<+>') operator is a synonym for ('<|>') from the
--   'Alternative' instance for 'Enumeration', which should be used in
--   preference to ('<+>').  ('<+>') is provided as a separate
--   standalone operator to make it easier to document.
--
-- >>> enumerate . takeE 10 $ singleton 17 <|> nat
-- [17,0,1,2,3,4,5,6,7,8]
--
-- >>> enumerate . takeE 10 $ nat <|> singleton 17
-- [17,0,1,2,3,4,5,6,7,8]
--
-- >>> enumerate . takeE 10 $ nat <|> (negate <$> nat)
-- [0,0,1,-1,2,-2,3,-3,4,-4]
--
--   Note that this is not associative in a strict sense.  In
--   particular, it may fail to be associative when mixing finite and
--   infinite enumerations:
--
-- >>> enumerate . takeE 10 $ nat <|> (singleton 17 <|> nat)
-- [0,17,1,0,2,1,3,2,4,3]
--
-- >>> enumerate . takeE 10 $ (nat <|> singleton 17) <|> nat
-- [17,0,0,1,1,2,2,3,3,4]
--
-- However, it is associative in several weaker senses:
--
--   * If all the enumerations are finite
--   * If all the enumerations are infinite
--   * If enumerations are considered equivalent up to reordering
--     (they are not, but considering them so may be acceptable in
--     some applications).
(<+>) :: Enumeration a -> Enumeration a -> Enumeration a
e1 <+> e2 = case (card e1, card e2) of

  -- optimize for void <+> e2.
  (Finite 0, _)  -> e2

  -- Note we don't want to add a case for e1 <+> void right away since
  -- that would require forcing the cardinality of e2, and we'd rather
  -- let the following case work lazily in the cardinality of e2.

  -- First enumeration is finite: just put it first
  (Finite k1, _) -> Enumeration
    { card   = card e1 + card e2
    , select = \k -> if k < k1 then select e1 k else select e2 (k - k1)
    }

  -- First is infinite but second is finite: put all the second values first
  (_, Finite _) -> e2 <+> e1

  -- Both are infinite: use a fair (alternating) interleaving
  _ -> interleave (Enumeration 2 (\case {0 -> e1; 1 -> e2}))

-- | One half of the isomorphism between \(\mathbb{N}\) and
--   \(\mathbb{N} \times \mathbb{N}\) which enumerates by diagonals:
--   turn a particular natural number index into its position in the
--   2D grid.  That is, given this numbering of a 2D grid:
--
--   @
--   0 1 3 6 ...
--   2 4 7
--   5 8
--   9
--   @
--
--   'diagonal' maps \(0 \mapsto (0,0), 1 \mapsto (0,1), 2 \mapsto (1,0) \dots\)
diagonal :: Integer -> (Integer, Integer)
diagonal k = (k - t, d - (k - t))
  where
    d = (integerSqrt (1 + 8*k) - 1) `div` 2
    t = d*(d+1) `div` 2

-- | Cartesian product of enumerations. If both are finite, uses a
--   simple lexicographic ordering.  If only one is finite, the
--   resulting enumeration is still in lexicographic order, with the
--   infinite enumeration as the most significant component.  For two
--   infinite enumerations, uses a fair 'diagonal' interleaving.
--
-- >>> enumerate $ finiteList [1..3] >< finiteList "abcd"
-- [(1,'a'),(1,'b'),(1,'c'),(1,'d'),(2,'a'),(2,'b'),(2,'c'),(2,'d'),(3,'a'),(3,'b'),(3,'c'),(3,'d')]
--
-- >>> enumerate . takeE 10 $ finiteList "abc" >< nat
-- [('a',0),('b',0),('c',0),('a',1),('b',1),('c',1),('a',2),('b',2),('c',2),('a',3)]
--
-- >>> enumerate . takeE 10 $ nat >< finiteList "abc"
-- [(0,'a'),(0,'b'),(0,'c'),(1,'a'),(1,'b'),(1,'c'),(2,'a'),(2,'b'),(2,'c'),(3,'a')]
--
-- >>> enumerate . takeE 10 $ nat >< nat
-- [(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),(0,3),(1,2),(2,1),(3,0)]
--
--   Like ('<+>'), this operation is also not associative (not even up
--   to reassociating tuples).
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

------------------------------------------------------------
-- Building standard data types
------------------------------------------------------------

-- | Enumerate all possible values of type `Maybe a`, where the values
--   of type `a` are taken from the given enumeration.
--
-- >>> enumerate $ maybeOf (finiteList [1,2,3])
-- [Nothing,Just 1,Just 2,Just 3]
maybeOf :: Enumeration a -> Enumeration (Maybe a)
maybeOf e = singleton Nothing <|> Just <$> e

-- | Enumerae all possible values of type @Either a b@ with inner values
--   taken from the given enumerations.
--
-- >>> enumerate . takeE 6 $ eitherOf nat nat
-- [Left 0,Right 0,Left 1,Right 1,Left 2,Right 2]
eitherOf :: Enumeration a -> Enumeration b -> Enumeration (Either a b)
eitherOf e1 e2 = Left <$> e1 <|> Right <$> e2

-- | Enumerate all possible lists containing values from the given enumeration.
--
-- >>> enumerate . takeE 15 $ listOf nat
-- [[],[0],[0,0],[1],[0,0,0],[1,0],[2],[0,1],[1,0,0],[2,0],[3],[0,0,0,0],[1,1],[2,0,0],[3,0]]
listOf :: Enumeration a -> Enumeration [a]
listOf e = case card e of
  Finite 0 -> empty
  _        -> listOfE
    where
      listOfE = infinite $ singleton [] <|> (:) <$> e <*> listOfE


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
        last $ takeWhile ((n>=) . snd) $ zip (1:twopows) twopows
      newtonStep x = div (x + div n x) 2
      iters = iterate newtonStep (integerSqrt (div n lowerN ) * lowerRoot)
      isRoot r = r^!2 <= n && n < (r+1)^!2
  in  head $ dropWhile (not . isRoot) iters

(^!) :: Num a => a -> Int -> a
(^!) x n = x^n
