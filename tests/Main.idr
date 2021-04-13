||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Test.Golden

%default total

tests : TestPool
tests =
  MkTestPool
  []
  [ "000-hello-world"
  , "001-scrub"
  , "002-split"
  , "003-gates"
  , "004-for"
  ]

covering
main : IO ()
main = runner [tests]


-- [ EOF ]
