module SystemV.Params.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Params
import SystemV.Params.DSL

import SystemV.Params.Pretty

namespace Params
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Param"

         rawast <- IO.timeToTryOrDie (timing opts)
                                     "LOG : Parsing Complete"
                                     Params.fromFile
                                     (getFirstFile opts)

         dump (debug opts) $ do prettyHeader "Raw AST"
                                printLn rawast

         ast <- Run.timeToTryOrDie (timing opts)
                                   "LOG : Elaboration "
                                   Params.elab
                                   rawast

         dump (debug opts) $ do prettyHeader "AST"
                                printLn ast

         term <- Run.timeToTryOrDie (timing opts)
                                    "LOG : Static Typing Complete "
                                    Params.build
                                    ast

         dump (debug opts) $ do prettyHeader "Term"
                                printLn term

         res <- Dep.timeToTryOrDie (timing opts)
                                   "LOG : Is in Normal Form "
                                   Params.nf
                                   term

         v <- Run.timeToTryOrDie (timing opts)
                                 "LOG : Runtime Checking Complete "
                                 Params.eval
                                 term

         dump (debug opts) $ do prettyHeader "Value"
                                printLn v

         putStrLn "LOG : Exiting Param"


-- [ EOF ]
