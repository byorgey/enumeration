{-# LANGUAGE DeriveFunctor #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Enumeration.Sized
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
-- Enumerations are isomorphic to lists, so many functions in this
-- module have the same name as common list functions.  It is
-- recommended to import this module qualified, e.g. XXX
--
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase    #-}

module Data.Enumeration.Sized
  ( -- * Sized enumerations

    SizedEnumeration

  , -- ** Constructing

    void, unit
  , singleton

  ) where

import           Prelude          hiding (drop, zipWith)

import qualified Data.Enumeration as E

------------------------------------------------------------
-- Sized enumerations

-- XXX we're probably going to run into the same problems as FEAT with
-- memoization etc.  Is it worth doing this sized stuff?  Can we make
-- recursively defined (but unsized) enumerations?

-- | A sized enumeration is just an enumeration of enumerations: the
--   outer enumeration enumerates by size; the inner ones enumerate
--   the elements of each given size.
newtype SizedEnumeration a = SE (E.Enumeration (E.Enumeration a))

-- | The empty sized enumeration, with no elements of any size.
void :: SizedEnumeration a
void = SE E.void

-- | The sized enumeration which contains only the single value @()@
--   of size 0.
unit :: SizedEnumeration ()
unit = SE (E.unit <$ E.unit)

-- | The sized enumeration which contains only the single given value,
--   considered to have size 1.
singleton :: a -> SizedEnumeration a
singleton a = SE (E.singleton E.void E.+++ E.singleton (E.singleton a))

-- finiteList --- yield all structures of size 0?

-- | XXX
(+++) :: SizedEnumeration a -> SizedEnumeration a -> SizedEnumeration a
SE e1 +++ SE e2 = SE $ E.zipWith (E.+++) e1 e2

-- | XXX
(><) :: SizedEnumeration a -> SizedEnumeration b -> SizedEnumeration (a,b)
(SE e1) >< (SE e2) = SE $ E.Enumeration
  (E.card e1 + E.card e2)
  (\sz -> E.concat ((\k -> E.select e1 (sz - k) E.>< E.select e2 k) <$> E.finite (sz + 1)))

-- (+++) : zip with + by size
-- (><)  : convolution by size

-- Put this into a separate library

