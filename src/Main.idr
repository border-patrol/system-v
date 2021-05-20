module Main

import System

import SystemV.Common.Options

import SystemV.Core.Run
import SystemV.Annotated.Run
import SystemV.HigherOrder.Run

exec : Mode -> Opts -> IO ()
exec CORE        = Core.run
exec ANNOTATED   = Annotated.run
exec HIGHERORDER = HigherOrder.run

main : IO ()
main
  = do putStrLn "LOG : Starting SystemV "
       Right (m,opts) <- processArgs
         | Left err => do printLn err
                          exitFailure
       exec m opts
       putStrLn "LOG : Bye"

-- [ EOF ]
