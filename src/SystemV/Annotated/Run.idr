module SystemV.Annotated.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Annotated
import SystemV.Annotated.DSL

namespace Annotated
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Annotated"
         Right ast <- Annotated.fromFile (getFirstFile opts)
           | Left err => printLn err
         putStrLn "LOG : Parsing Complete"

         term <- timeToTryOrDie (timing opts)
                                "LOG : Typing Complete "
                                Annotated.build
                                ast
         v <- timeToTryOrDie (timing opts)
                             "LOG : Evaluating "
                             Annotated.eval
                             term
         putStrLn "LOG : Exiting Annotated"


-- [ EOF ]
