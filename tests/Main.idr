||| Borrowed From Idris2 and improved with Test.Unit
module Main

import Test.Golden

%default total

testPaths : String -> TestPool -> TestPool
testPaths dir
  = record { testCases $= map ((dir ++ "/") ++) }

namespace Param
  export
  tests : TestPool
  tests
    = MkTestPool -- "Params"
                 []
                 [ "000-hello-world"
                 , "001-scrub"
                 , "002-split"
                 , "003-gates"
                 , "004-for"
                 ]

namespace Core
  export
  tests : TestPool
  tests
    = MkTestPool --"Core Language"
                 []
                 [ "000-hello-world"
                 , "001-scrub"
                 , "002-split"
                 , "003-gates"
                 ]

covering
main : IO ()
main
  = runner [ testPaths "core" Core.tests
           --, testPaths "param" Param.tests
           ]



-- [ EOF ]
