||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Test.Golden

%default total

testPaths : String -> TestPool -> TestPool
testPaths dir
  = record { testCases $= map ((dir ++ "/") ++) }

namespace Common
  export
  tests : TestPool
  tests
    = MkTestPool "Common"
                 []
                 Nothing
                 [ "001-swap"
                 , "002-scrub"
                 , "003-split"
                 , "004-gates"
                 , "005-flipflop"
                 , "006-adders"
                 , "007-nand"
                 ]

namespace Param
  export
  tests : TestPool
  tests
    = MkTestPool "Params"
                 []
                 Nothing
                 [ "000-swap"
                 , "001-scrub"
                 , "002-split"
                 , "003-adders"
                 , "004-for"
                 , "005-nand"
                 ]

namespace Annotated
  export
  tests : TestPool
  tests
    = MkTestPool "Annotated"
                 []
                 Nothing
                 [ "000-hello-world"
                 , "001-scrub"
                 , "002-gates"
                 , "003-flipflops"
                 ]

namespace HigherOrder
  export
  tests : TestPool
  tests
    = MkTestPool "Higher Order Language"
                 []
                 Nothing
                 [ "000-higher-order-and"
                 , "001-testbench"
                 ]

covering
main : IO ()
main
  = runner [ testPaths "common"       Common.tests
           , testPaths "annotated"    Annotated.tests
           , testPaths "higher-order" HigherOrder.tests
           , testPaths "param"        Param.tests
           ]



-- [ EOF ]
