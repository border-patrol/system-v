module SystemV.HigherOrder.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.HigherOrder
import SystemV.HigherOrder.DSL

namespace HigherOrder
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Core"
         Right ast <- HigherOrder.fromFile (getFirstFile opts)
           | Left err => printLn err
         putStrLn "LOG : Parsing Complete"

         term <- timeToTryOrDie (timing opts)
                                "LOG: Typing Complete "
                                HigherOrder.build
                                ast
         v <- timeToTryOrDie (timing opts)
                             "LOG: Evaluating "
                             HigherOrder.eval
                             term
         putStrLn "LOG : Exiting Core"


-- [ EOF ]
