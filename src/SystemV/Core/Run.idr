module SystemV.Core.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Core
import SystemV.Core.DSL

namespace Core
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Core"
         Right ast <- Core.fromFile (getFirstFile opts)
           | Left err => printLn err
         putStrLn "LOG : Parsing Complete"

         term <- timeToTryOrDie (timing opts)
                                "LOG: Typing Complete "
                                Core.build
                                ast
         v <- timeToTryOrDie (timing opts)
                             "LOG: Evaluating "
                             Core.eval
                             term
         putStrLn "LOG : Exiting Core"


-- [ EOF ]
