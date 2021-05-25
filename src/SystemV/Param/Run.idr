module SystemV.Param.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Param
import SystemV.Param.DSL

namespace Param
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Param"
         Right rawast <- Param.fromFile (getFirstFile opts)
           | Left err => printLn err
         putStrLn "LOG : Parsing Complete"

         ast <- timeToTryOrDie (timing opts)
                               "LOG : Elaboration "
                               Param.elab
                               rawast

         term <- timeToTryOrDie (timing opts)
                                "LOG : Static Typing Complete "
                                Param.build
                                ast
--         v <- timeToTryOrDie (timing opts)
--                             "LOG : Evaluating "
--                             Param.eval
--                             term
         putStrLn "LOG : Exiting Param"


-- [ EOF ]
