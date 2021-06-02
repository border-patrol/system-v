module SystemV.Core.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Core
import SystemV.Core.DSL
import SystemV.Core.Pretty

namespace Core
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Core"

         ast <- IO.timeToTryOrDie (timing opts)
                                  "LOG : Parsing Complete"
                                  Core.fromFile
                                  (getFirstFile opts)

         dump (debug opts) $ do prettyHeader "AST"
                                printLn ast

         term <- Run.timeToTryOrDie (timing opts)
                                    "LOG : Typing Complete "
                                    Core.build
                                    ast

         dump (debug opts) $ do prettyHeader "Term"
                                printLn term

         res <- Dep.timeToTryOrDie (timing opts)
                                   "LOG : Is in Normal Form "
                                   Core.nf
                                   term

         v <- Run.timeToTryOrDie (timing opts)
                                 "LOG : Evaluating "
                                 Core.eval
                                 term

         dump (debug opts) $ do prettyHeader "Value"
                                printLn v


         putStrLn "LOG : Exiting Core"


-- [ EOF ]
