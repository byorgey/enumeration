{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- SPDX-License-Identifier: BSD-3-Clause

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Enumeration.Invertible
-- Copyright   :  Brent Yorgey
-- Maintainer  :  byorgey@gmail.com
--
-- An /invertible enumeration/ is a bijection between a set of values
-- and the natural numbers (or a finite prefix thereof), represented
-- as a pair of inverse functions, one in each direction.  Hence they
-- support efficient indexing and can be constructed for very large
-- finite sets.  A few examples are shown below.
--
-- Compared to "Data.Enumeration", one can also build invertible
-- enumerations of functions (or other type formers with contravariant
-- arguments); however, invertible enumerations no longer make for
-- valid 'Functor', 'Applicative', or 'Alternative' instances.
--
-- This module exports many of the same names as "Data.Enumeration";
-- the expectation is that you will choose one or the other to import,
-- though of course it is possible to import both if you qualify the
-- imports.
--
-----------------------------------------------------------------------------

module Data.Enumeration.Invertible
  ( -- * Invertible enumerations

    IEnumeration

    -- ** Using enumerations

  , Cardinality(..), card
  , Index, select, locate

  , isFinite
  , enumerate

    -- ** Primitive enumerations

  , void
  , unit
  , singleton
  , finite
  , finiteList
  , boundedEnum

  , nat
  , int
  , cw
  , rat

  -- ** Enumeration combinators

  , mapE
  , takeE, dropE
  , zipE
  , infinite
  , (<+>)
  , (><)
  , interleave

  , maybeOf
  , eitherOf
  , listOf
  , finiteSubsetOf
  , finiteEnumerationOf
  , functionOf

  -- * Utilities

  , undiagonal
  ) where

import           Control.Applicative (Alternative (..))
import           Data.Bits           (shiftL, (.|.))
import           Data.List           (findIndex, foldl')
import           Data.Maybe          (fromJust)
import           Data.Ratio

import           Data.Enumeration    (Cardinality (..), Enumeration, Index)
import qualified Data.Enumeration    as E

------------------------------------------------------------
-- Setup for doctest examples
------------------------------------------------------------

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Control.Arrow ((&&&))
-- >>> :{
--   data Tree = L | B Tree Tree deriving Show
--   treesUpTo :: Int -> IEnumeration Tree
--   treesUpTo 0 = singleton L
--   treesUpTo n = mapE toTree fromTree (unit <+> (t' >< t'))
--     where
--       t' = treesUpTo (n-1)
--   trees :: IEnumeration Tree
--   trees = infinite $ mapE toTree fromTree (unit <+> (trees >< trees))
--   toTree :: Either () (Tree, Tree) -> Tree
--   toTree = either (const L) (uncurry B)
--   fromTree :: Tree -> Either () (Tree, Tree)
--   fromTree L = Left ()
--   fromTree (B l r) = Right (l,r)
-- :}

------------------------------------------------------------
-- Invertible enumerations
------------------------------------------------------------

-- | An invertible enumeration is a bijection between a set of
--   enumerated values and the natural numbers, or a finite prefix of
--   the natural numbers.  An invertible enumeration is represented as
--   a function from natural numbers to values, paired with an inverse
--   function that returns the natural number index of a given value.
--   Enumerations can thus easily be constructed for very large sets,
--   and support efficient indexing and random sampling.
--
--   Note that 'IEnumeration' cannot be made an instance of 'Functor',
--   'Applicative', or 'Alternative'.  However, it does support the
--   'functionOf' combinator which cannot be supported by
--   "Data.Enumeration".

data IEnumeration a = IEnumeration
  { baseEnum :: Enumeration a
    -- | Compute the index of a particular value in its enumeration.
    --   Note that the result of 'locate' is only valid when given a
    --   value which is actually in the range of the enumeration.
  , locate   :: a -> Index
  }

-- | Map a pair of inverse functions over an invertible enumeration of
--   @a@ values to turn it into an invertible enumeration of @b@
--   values.  Because invertible enumerations contain a /bijection/ to
--   the natural numbers, we really do need both directions of a
--   bijection between @a@ and @b@ in order to map.  This is why
--   'IEnumeration' cannot be an instance of 'Functor'.
mapE :: (a -> b) -> (b -> a) -> IEnumeration a -> IEnumeration b
mapE f g (IEnumeration e l) = IEnumeration (f <$> e) (l . g)

------------------------------------------------------------
-- Using enumerations
------------------------------------------------------------

-- | Select the value at a particular index.  Precondition: the index
--   must be strictly less than the cardinality.
select :: IEnumeration a -> (Index -> a)
select = E.select . baseEnum

-- | Get the cardinality of an enumeration.
card :: IEnumeration a -> Cardinality
card = E.card . baseEnum

-- | Test whether an enumeration is finite.
--
-- >>> isFinite (finiteList [1,2,3])
-- True
--
-- >>> isFinite nat
-- False
isFinite :: IEnumeration a -> Bool
isFinite (IEnumeration e _) = E.isFinite e

-- | List the elements of an enumeration in order.  Inverse of
--   'finiteList'.
enumerate :: IEnumeration a -> [a]
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
void :: IEnumeration a
void = IEnumeration empty (error "locate void")

-- | The unit enumeration, with a single value of @()@ at index 0.
--
-- >>> card unit
-- Finite 1
--
-- >>> enumerate unit
-- [()]
--
-- >>> locate unit ()
-- 0
unit :: IEnumeration ()
unit = IEnumeration E.unit (const 0)

-- | An enumeration of a single given element at index 0.
--
-- >>> card (singleton 17)
-- Finite 1
--
-- >>> enumerate (singleton 17)
-- [17]
--
-- >>> locate (singleton 17) 17
-- 0
singleton :: a -> IEnumeration a
singleton a = IEnumeration (E.singleton a) (const 0)

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
--
-- >>> locate (finite 5) 2
-- 2
finite :: Integer -> IEnumeration Integer
finite n = IEnumeration (E.finite n) id

-- | Construct an enumeration from the elements of a /finite/ list.
--   The elements of the list must all be distinct. To turn an
--   enumeration back into a list, use 'enumerate'.
--
-- >>> enumerate (finiteList [2,3,8,1])
-- [2,3,8,1]
-- >>> select (finiteList [2,3,8,1]) 2
-- 8
-- >>> locate (finiteList [2,3,8,1]) 8
-- 2
--
--   'finiteList' does not work on infinite lists: inspecting the
--   cardinality of the resulting enumeration (something many of the
--   enumeration combinators need to do) will hang trying to compute
--   the length of the infinite list.
--
--   'finiteList' uses ('!!') and 'findIndex' internally (which both
--   take $O(n)$ time), so you probably want to avoid using it on long
--   lists.  It would be possible to make a version with better
--   indexing performance by allocating a vector internally, but I am
--   too lazy to do it.  If you have a good use case let me know
--   (better yet, submit a pull request).
finiteList :: Eq a => [a] -> IEnumeration a
finiteList as = IEnumeration (E.finiteList as) locateFinite
  -- Note the use of !! and findIndex is not very efficient, but for
  -- small lists it probably still beats the overhead of allocating a
  -- vector.  Most likely this will only ever be used with very small
  -- lists anyway.  If it becomes a problem we could add another
  -- combinator that behaves just like finiteList but allocates a
  -- Vector internally.

  where
    locateFinite a = fromIntegral . fromJust $ findIndex (==a) as

-- | Enumerate all the values of a bounded 'Enum' instance.
--
-- >>> enumerate (boundedEnum @Bool)
-- [False,True]
--
-- >>> select (boundedEnum @Char) 97
-- 'a'
-- >>> locate (boundedEnum @Char) 'Z'
-- 90
--
-- >>> card (boundedEnum @Int)
-- Finite 18446744073709551616
-- >>> select (boundedEnum @Int) 0
-- -9223372036854775808
boundedEnum :: forall a. (Enum a, Bounded a) => IEnumeration a
boundedEnum = IEnumeration E.boundedEnum (subtract lo . fromIntegral . fromEnum)
  where
    lo :: Index
    lo = fromIntegral (fromEnum (minBound @a))

-- | The natural numbers, @0, 1, 2, ...@.
--
-- >>> enumerate . takeE 10 $ nat
-- [0,1,2,3,4,5,6,7,8,9]
nat :: IEnumeration Integer
nat = IEnumeration E.nat id

-- | All integers in the order @0, 1, -1, 2, -2, 3, -3, ...@.
int :: IEnumeration Integer
int = IEnumeration E.int locateInt
  where
    locateInt z
      | z <= 0    = 2 * abs z
      | otherwise = 2*z - 1

-- | The positive rational numbers, enumerated according to the
--   [Calkin-Wilf sequence](http://www.cs.ox.ac.uk/publications/publication1664-abstract.html).
--
-- >>> enumerate . takeE 10 $ cw
-- [1 % 1,1 % 2,2 % 1,1 % 3,3 % 2,2 % 3,3 % 1,1 % 4,4 % 3,3 % 5]
-- >>> locate cw (3 % 2)
-- 4
-- >>> locate cw (23 % 99)
-- 3183
cw :: IEnumeration Rational
cw = IEnumeration E.cw (pred . locateCW)
  where
    locateCW r = go (numerator r, denominator r)
    go (1,1) = 1
    go (a,b)
      | a < b     = 2 * go (a, b - a)
      | otherwise = 1 + 2 * go (a - b, b)

-- | An enumeration of all rational numbers: 0 first, then each
--   rational in the Calkin-Wilf sequence followed by its negative.
--
-- >>> enumerate . takeE 10 $ rat
-- [0 % 1,1 % 1,(-1) % 1,1 % 2,(-1) % 2,2 % 1,(-2) % 1,1 % 3,(-1) % 3,3 % 2]
-- >>> locate rat (-45 % 61)
-- 2540

rat :: IEnumeration Rational
rat = mapE
  (either (const 0) (either id negate))
  unrat
  (unit <+> (cw <+> cw))
  where
    unrat 0 = Left ()
    unrat r
      | r > 0     = Right (Left r)
      | otherwise = Right (Right (-r))

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
takeE :: Integer -> IEnumeration a -> IEnumeration a
takeE k (IEnumeration e l) = IEnumeration (E.takeE k e) l

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
dropE :: Integer -> IEnumeration a -> IEnumeration a
dropE k (IEnumeration e l) = IEnumeration (E.dropE k e) (subtract (max 0 k) . l)

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
-- toTree :: Either () (Tree, Tree) -> Tree
-- toTree = either (const L) (uncurry B)
--
-- fromTree :: Tree -> Either () (Tree, Tree)
-- fromTree L       = Left ()
-- fromTree (B l r) = Right (l,r)
--
-- treesBad :: IEnumeration Tree
-- treesBad = mapE toTree fromTree (unit '<+>' (treesBad '><' treesBad))
--
-- trees :: IEnumeration Tree
-- trees = infinite $ mapE toTree fromTree (unit '<+>' (trees '><' trees))
-- @
--
--   Trying to use @treesBad@ at all will simply hang, since trying to
--   compute its cardinality leads to infinite recursion.
--
-- @
-- \>>>\ select treesBad 5
-- ^CInterrupted.
-- @
--
--   However, using 'infinite', as in the definition of @trees@,
--   provides the needed laziness:
--
-- >>> card trees
-- Infinite
-- >>> enumerate . takeE 3 $ trees
-- [L,B L L,B L (B L L)]
-- >>> select trees 87239862967296
-- B (B (B (B (B L L) (B (B (B L L) L) L)) (B L (B L (B L L)))) (B (B (B L (B L (B L L))) (B (B L L) (B L L))) (B (B L (B L (B L L))) L))) (B (B L (B (B (B L (B L L)) (B L L)) L)) (B (B (B L (B L L)) L) L))
-- >>> select trees 123
-- B (B L (B L L)) (B (B L (B L L)) (B L (B L L)))
-- >>> locate trees (B (B L (B L L)) (B (B L (B L L)) (B L (B L L))))
-- 123

infinite :: IEnumeration a -> IEnumeration a
infinite (IEnumeration e l) = IEnumeration (E.infinite e) l

-- | Fairly interleave a set of /infinite/ enumerations.
--
--   For a finite set of infinite enumerations, a round-robin
--   interleaving is used. That is, if we think of an enumeration of
--   enumerations as a 2D matrix read off row-by-row, this corresponds
--   to taking the transpose of a matrix with finitely many infinite
--   rows, turning it into one with infinitely many finite rows.  For
--   an infinite set of infinite enumerations, /i.e./ an infinite 2D
--   matrix, the resulting enumeration reads off the matrix by
--   'Data.Enumeration.diagonal's.
--
--   Note that the type of this function is slightly different than
--   its counterpart in "Data.Enumeration": each enumerated value in
--   the output is tagged with an index indicating which input
--   enumeration it came from.  This is required to make the result
--   invertible, and is analogous to the way the output values of
--   '<+>' are tagged with 'Left' or 'Right'; in fact, 'interleave'
--   can be thought of as an iterated version of '<+>', but with a
--   more efficient implementation.

interleave :: IEnumeration (IEnumeration a) -> IEnumeration (Index, a)
interleave e = IEnumeration
  { baseEnum = E.mkEnumeration Infinite $ \k ->
      let (i,j) = case card e of
            Finite n -> k `divMod` n
            Infinite -> E.diagonal k
      in  (j, select (select e j) i)
  , locate   = \(j, a) ->
      let i = locate (select e j) a
      in  case card e of
            Finite n -> i*n + j
            Infinite -> undiagonal (i,j)
  }

-- | Zip two enumerations in parallel, producing the pair of
--   elements at each index.  The resulting enumeration is truncated
--   to the cardinality of the smaller of the two arguments.
--
--   Note that defining @zipWithE@ as in "Data.Enumeration" is not
--   possible since there would be no way to invert it in general.
--   However, one can use 'zipE' in combination with 'mapE' to achieve
--   a similar result.
--
-- >>> enumerate $ zipE nat (boundedEnum @Bool)
-- [(0,False),(1,True)]
--
-- >>> cs = mapE (uncurry replicate) (length &&& head) (zipE (finiteList [1..10]) (dropE 35 (boundedEnum @Char)))
-- >>> enumerate cs
-- ["#","$$","%%%","&&&&","'''''","((((((",")))))))","********","+++++++++",",,,,,,,,,,"]
-- >>> locate cs "********"
-- 7

zipE :: IEnumeration a -> IEnumeration b -> IEnumeration (a,b)
zipE ea eb = IEnumeration
  { baseEnum = E.zipE (baseEnum ea) (baseEnum eb)
  , locate   = locate ea . fst
  }

-- | Sum, /i.e./ disjoint union, of two enumerations.  If both are
--   finite, all the values of the first will be enumerated before the
--   values of the second.  If only one is finite, the values from the
--   finite enumeration will be listed first.  If both are infinite, a
--   fair (alternating) interleaving is used, so that every value ends
--   up at a finite index in the result.
--
--   Note that this has a different type than the version in
--   "Data.Enumeration".  Here we require the output to carry an
--   explicit 'Either' tag to make it invertible.
--
-- >>> enumerate . takeE 5 $ singleton 17 <+> nat
-- [Left 17,Right 0,Right 1,Right 2,Right 3]
--
-- >>> enumerate . takeE 5 $ nat <+> singleton 17
-- [Right 17,Left 0,Left 1,Left 2,Left 3]
--
-- >>> enumerate . takeE 5 $ nat <+> nat
-- [Left 0,Right 0,Left 1,Right 1,Left 2]
--
-- >>> locate (nat <+> nat) (Right 35)
-- 71

(<+>) :: IEnumeration a -> IEnumeration b -> IEnumeration (Either a b)
a <+> b = IEnumeration (Left <$> baseEnum a <|> Right <$> baseEnum b) (locateEither a b)
  where
    locateEither :: IEnumeration a -> IEnumeration b -> (Either a b -> Index)
    locateEither a b = case (card a, card b) of
      (Finite k1, _) -> either (locate a) ((+k1) . locate b)
      (_, Finite k2) -> either ((+k2) . locate a) (locate b)
      _              -> either ((*2) . locate a) (succ . (*2) . locate b)


-- | The other half of the isomorphism between \(\mathbb{N}\) and
--   \(\mathbb{N} \times \mathbb{N}\) which enumerates by diagonals:
--   turn a pair of natural numbers giving a position in the 2D grid
--   into the number in the cell, according to this numbering scheme:
--
--   @
--   0 1 3 6 ...
--   2 4 7
--   5 8
--   9
--   @
undiagonal :: (Integer, Integer) -> Integer
undiagonal (r,c) = (r+c) * (r+c+1) `div` 2 + r

-- | Cartesian product of enumerations. If both are finite, uses a
--   simple lexicographic ordering.  If only one is finite, the
--   resulting enumeration is still in lexicographic order, with the
--   infinite enumeration as the most significant component.  For two
--   infinite enumerations, uses a fair 'Data.Enumeration.diagonal' interleaving.
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
-- >>> locate (nat >< nat) (1,1)
-- 4
-- >>> locate (nat >< nat) (36,45)
-- 3357
--
--   Like ('<+>'), this operation is also not associative (not even up
--   to reassociating tuples).
(><) :: IEnumeration a -> IEnumeration b -> IEnumeration (a,b)
a >< b = IEnumeration (baseEnum a E.>< baseEnum b) (locatePair a b)
  where
    locatePair :: IEnumeration a -> IEnumeration b -> ((a,b) -> Index)
    locatePair a b = case (card a, card b) of
      (_, Finite k2) -> \(x,y) -> k2 * locate a x + locate b y
      (Finite k1, _) -> \(x,y) -> k1 * locate b y + locate a x
      _              -> \(x,y) -> undiagonal (locate a x, locate b y)

------------------------------------------------------------
-- Building standard data types
------------------------------------------------------------

-- | Enumerate all possible values of type `Maybe a`, where the values
--   of type `a` are taken from the given enumeration.
--
-- >>> enumerate $ maybeOf (finiteList [1,2,3])
-- [Nothing,Just 1,Just 2,Just 3]
-- >>> locate (maybeOf (maybeOf (finiteList [1,2,3]))) (Just (Just 2))
-- 3
maybeOf :: IEnumeration a -> IEnumeration (Maybe a)
maybeOf a = mapE (either (const Nothing) Just) (maybe (Left ()) Right) (unit <+> a)

-- | Enumerae all possible values of type @Either a b@ with inner values
--   taken from the given enumerations.
--
--   Note that for invertible enumerations, 'eitherOf' is simply a
--   synonym for '<+>'.
--
-- >>> enumerate . takeE 6 $ eitherOf nat nat
-- [Left 0,Right 0,Left 1,Right 1,Left 2,Right 2]
eitherOf :: IEnumeration a -> IEnumeration b -> IEnumeration (Either a b)
eitherOf = (<+>)

-- | Enumerate all possible finite lists containing values from the
-- given enumeration.
--
-- >>> enumerate . takeE 15 $ listOf nat
-- [[],[0],[0,0],[1],[0,0,0],[1,0],[2],[0,1],[1,0,0],[2,0],[3],[0,0,0,0],[1,1],[2,0,0],[3,0]]
-- >>> locate (listOf nat) [3,4,20,5,19]
-- 666270815854068922513792635440014
listOf :: IEnumeration a -> IEnumeration [a]
listOf a = case card a of
  Finite 0 -> singleton []
  _        -> listOfA
    where
      listOfA = infinite $
        mapE (either (const []) (uncurry (:))) uncons (unit <+> (a >< listOfA))
      uncons []     = Left ()
      uncons (a:as) = Right (a, as)

-- | Enumerate all possible finite subsets of values from the given
--   enumeration.  The elements in each list will always occur in
--   increasing order of their index in the given enumeration.
--
-- >>> enumerate $ finiteSubsetOf (finite 3)
-- [[],[0],[1],[0,1],[2],[0,2],[1,2],[0,1,2]]
--
-- >>> locate (finiteSubsetOf nat) [2,3,6,8]
-- 332
-- >>> 332 == 2^8 + 2^6 + 2^3 + 2^2
-- True
finiteSubsetOf :: IEnumeration a -> IEnumeration [a]
finiteSubsetOf a = IEnumeration (E.finiteSubsetOf (baseEnum a)) unpick
  where
    unpick = foldl' (.|.) 0 . map ((1 `shiftL`) . fromIntegral . locate a)

-- | @finiteEnumerationOf n a@ creates an enumeration of all sequences
--   of exactly n items taken from the enumeration @a@.
--
-- >>> map E.enumerate . enumerate $ finiteEnumerationOf 2 (finite 3)
-- [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2],[2,0],[2,1],[2,2]]
--
-- >>> map E.enumerate . take 10 . enumerate $ finiteEnumerationOf 3 nat
-- [[0,0,0],[0,0,1],[1,0,0],[0,1,0],[1,0,1],[2,0,0],[0,0,2],[1,1,0],[2,0,1],[3,0,0]]
finiteEnumerationOf :: Int -> IEnumeration a -> IEnumeration (Enumeration a)
finiteEnumerationOf 0 _ = singleton empty
finiteEnumerationOf n a = case card a of
  Finite k -> IEnumeration (E.finiteEnumerationOf n (baseEnum a)) (locateEnum k)
  Infinite -> foldr prod (singleton empty) (replicate n a)

  where
    locateEnum k = fromBase k . reverse . E.enumerate . fmap (locate a)

    fromBase k = foldr (\d r -> d + k*r) 0

    prod :: IEnumeration a -> IEnumeration (Enumeration a) -> IEnumeration (Enumeration a)
    prod a as = mapE (\(a,e) -> E.singleton a <|> e) (\e -> (E.select e 0, E.dropE 1 e))
                  (a >< as)

-- | @functionOf a b@ creates an enumeration of all functions taking
--   values from the enumeration @a@ and returning values from the
--   enumeration @b@.  As a precondition, @a@ must be finite;
--   otherwise @functionOf@ throws an error. There are two exceptions:
--   first, if @b@ has cardinality 1, we get an enumeration of exactly
--   one function which constantly returns the one element of @b@,
--   even if @a@ is infinite.  Second, if @b@ has cardinality 0, we
--   get a singleton enumeration if @a@ also has cardinality 0, and an
--   empty enumeration otherwise (even if @a@ is infinite).
--
-- >>> bbs = functionOf (boundedEnum @Bool) (boundedEnum @Bool)
-- >>> card bbs
-- Finite 4
-- >>> map (select bbs 2) [False, True]
-- [True,False]
-- >>> locate bbs not
-- 2
--
-- >>> locate (functionOf bbs (boundedEnum @Bool)) (\f -> f True)
-- 5
--
-- >>> n2u = functionOf nat unit
-- >>> card n2u
-- Finite 1
-- >>> (select n2u 0) 57
-- ()
--
-- >>> n2o = functionOf nat void
-- >>> card n2o
-- Finite 0
-- >>> o2o = functionOf void void
-- >>> card o2o
-- Finite 1
functionOf :: IEnumeration a -> IEnumeration b -> IEnumeration (a -> b)
functionOf as bs = case card bs of
  Finite 1 -> singleton (\_ -> select bs 0)   -- 1^x = 1
  Finite 0 -> case card as of                 -- 0^0 = 1, 0^x = 0
    Finite 0 -> singleton (\_ -> error "called function with empty domain")
    _        -> void
  _        -> case card as of
    Infinite -> error "functionOf with infinite domain"
    Finite n -> mapE toFunc fromFunc (finiteEnumerationOf (fromIntegral n) bs)

  where
    toFunc bTuple a = E.select bTuple (locate as a)
    fromFunc f = f <$> baseEnum as
