module SystemV.Param.Run

import SystemV.Common.Run
import SystemV.Common.Options

import SystemV.Param
import SystemV.Param.DSL

import SystemV.Param.Pretty

namespace Param
  export
  run : Opts -> IO ()
  run opts
    = do putStrLn "LOG : Running SystemV Param"

         rawast <- timeToTryOrDie (timing opts)
                                  "LOG : Parsing Complete"
                                  Param.fromFile
                                  (getFirstFile opts)

         dump (debug opts) $ do prettyHeader "Raw AST"
                                printLn rawast

         ast <- timeToTryOrDie (timing opts)
                               "LOG : Elaboration "
                               Param.elab
                               rawast

         dump (debug opts) $ do prettyHeader "AST"
                                printLn ast

         term <- timeToTryOrDie (timing opts)
                                "LOG : Static Typing Complete "
                                Param.build
                                ast

         dump (debug opts) $ do prettyHeader "Term"
                                printLn term

         v <- timeToTryOrDie (timing opts)
                             "LOG : Runtime Checking Complete "
                             Param.eval
                             term

         dump (debug opts) $ do prettyHeader "Value"
                                printLn v

         putStrLn "LOG : Exiting Param"


-- [ EOF ]
