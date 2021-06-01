module SystemV.Annotated.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Annotated
import SystemV.Annotated.DSL

import SystemV.Annotated.Pretty

namespace Annotated
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Annotated"

         ast <- IO.timeToTryOrDie (timing opts)
                                  "LOG : Parsing Complete"
                                  Annotated.fromFile
                                  (getFirstFile opts)

         dump (debug opts) $ do prettyHeader "AST"
                                printLn ast

         term <- Run.timeToTryOrDie (timing opts)
                                    "LOG : Typing Complete "
                                    Annotated.build
                                    ast

         dump (debug opts) $ do prettyHeader "Term"
                                printLn term

         res <- Dep.timeToTryOrDie (timing opts)
                                   "LOG : Is in Normal Form "
                                   Annotated.nf
                                   term

         v <- Run.timeToTryOrDie (timing opts)
                                 "LOG : Evaluating "
                                 Annotated.eval
                                 term

         dump (debug opts) $ do prettyHeader "Value"
                                printLn v

         putStrLn "LOG : Exiting Annotated"


-- [ EOF ]
