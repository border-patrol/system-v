module SystemV.Params.Main

import System

import SystemV.Common.Options

import SystemV.Params.Run

main : IO ()
main
  = do putStrLn "LOG : Starting SystemV "

       Right (m,opts) <- processArgs
         | Left err => do printLn err
                          exitFailure
       Params.run opts
       putStrLn "LOG : Bye"

-- [ EOF ]
