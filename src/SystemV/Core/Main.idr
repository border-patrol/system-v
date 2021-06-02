module SystemV.Core.Main

import System

import SystemV.Common.Options

import SystemV.Core.Run

main : IO ()
main
  = do putStrLn "LOG : Starting SystemV "

       Right (m,opts) <- processArgs
         | Left err => do printLn err
                          exitFailure
       Core.run opts
       putStrLn "LOG : Bye"

-- [ EOF ]
