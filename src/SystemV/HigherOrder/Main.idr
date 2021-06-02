module SystemV.HigherOrder.Main

import System

import SystemV.Common.Options

import SystemV.HigherOrder.Run

main : IO ()
main
  = do putStrLn "LOG : Starting SystemV "

       Right (m,opts) <- processArgs
         | Left err => do printLn err
                          exitFailure
       HigherOrder.run opts
       putStrLn "LOG : Bye"

-- [ EOF ]
