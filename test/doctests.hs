import           Test.DocTest
main = doctest
  ["-isrc"
  ,"src/Data/Enumeration.hs"
  ,"src/Data/Enumeration/Invertible.hs"
  ,"src/Data/CoEnumeration.hs"
  ,"src/Data/ProEnumeration.hs"
  ,"--fast"
  ,"-package contravariant"
  ]
