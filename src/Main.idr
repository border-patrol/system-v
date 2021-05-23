module Main

import System

import SystemV.Common.Options

import SystemV.Core.Run
import SystemV.Annotated.Run
import SystemV.HigherOrder.Run
import SystemV.Param.Run

exec : Mode -> Opts -> IO ()
exec CORE        = Core.run
exec ANNOTATED   = Annotated.run
exec HIGHERORDER = HigherOrder.run
exec PARAM       = Param.run

main : IO ()
main
  = do putStrLn "LOG : Starting SystemV "
       Right (m,opts) <- processArgs
         | Left err => do printLn err
                          exitFailure
       exec m opts
       putStrLn "LOG : Bye"

-- [ EOF ]
