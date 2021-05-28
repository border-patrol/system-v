module SystemV.HigherOrder.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.HigherOrder
import SystemV.HigherOrder.DSL

import SystemV.HigherOrder.Pretty

namespace HigherOrder
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Core"

         ast <- timeToTryOrDie (timing opts)
                               "LOG : Parsing Complete"
                               HigherOrder.fromFile
                               (getFirstFile opts)

         dump (debug opts) $ do prettyHeader "AST"
                                printLn ast

         term <- timeToTryOrDie (timing opts)
                                "LOG: Typing Complete "
                                HigherOrder.build
                                ast

         dump (debug opts) $ do prettyHeader "Term"
                                printLn term

         v <- timeToTryOrDie (timing opts)
                             "LOG: Evaluating "
                             HigherOrder.eval
                             term

         dump (debug opts) $ do prettyHeader "Value"
                                printLn v

         putStrLn "LOG : Exiting Core"


-- [ EOF ]
