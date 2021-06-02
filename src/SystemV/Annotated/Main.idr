module SystemV.Annotated.Main

import System

import SystemV.Common.Options

import SystemV.Annotated.Run

main : IO ()
main
  = do putStrLn "LOG : Starting SystemV "

       Right (m,opts) <- processArgs
         | Left err => do printLn err
                          exitFailure
       Annotated.run opts
       putStrLn "LOG : Bye"

-- [ EOF ]
