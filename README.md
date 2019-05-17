# Lightweight, efficiently indexable enumerations

This package defines a type of *enumerations*, along with combinators
for building and manipulating them.  An enumeration is a finite or
countably infinite sequence of values, represented as a function from
an index to a value. Hence it is possible to work with even very large
finite sets.  Enumerations also naturally support (uniform) random
sampling.

Note the goal of this package is *not* to enumerate values of Haskell
types; there already exist many other packages to do that.  Rather,
the goal is simply to provide an abstract framework for working with
enumerations of any values at all.

See the documentation for examples; see the [announcement blog
post](https://byorgey.wordpress.com/2019/05/14/lightweight-efficiently-sampleable-enumerations-in-haskell/)
for additional examples and discussion.
