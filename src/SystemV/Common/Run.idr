module SystemV.Common.Run

import System
import System.File
import System.Clock

import Data.String

import Toolkit.System
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Run

%default total

%inline
export
printLog : Bool -> Clock type -> String -> IO ()
printLog True  t m = do putStr m
                        printLn t
printLog False t m = putStrLn m

namespace IO
  export
  timeToTryOrDie : Show err
                => Bool
                -> String
                -> (a -> IO (Either err type))
                -> a
                -> IO type
  timeToTryOrDie timing msg f a
      = do start <- clockTime UTC
           res <- f a
           case res of
             Left err => do stop <- clockTime UTC
                            putStrLn "Error Happened"
                            printLn err
                            let diff = timeDifference stop start
                            printLog timing diff msg
                            exitFailure
             Right res => do stop <- clockTime UTC
                             let diff =  timeDifference stop start
                             printLog timing diff msg
                             pure res
export
timeToTryOrDie : Show err
              => Bool
              -> String
              -> (a -> Either err type)
              -> a
              -> IO type
timeToTryOrDie timing msg f a
    = do start <- clockTime UTC
         case f a of
           Left err => do stop <- clockTime UTC
                          putStrLn "Error Happened"
                          printLn err
                          let diff = timeDifference stop start
                          printLog timing diff msg
                          exitFailure
           Right res => do stop <- clockTime UTC
                           let diff =  timeDifference stop start
                           printLog timing diff msg
                           pure res

namespace Dep
  export
  timeToTryOrDie : {a : Type} -> {type : a -> Type}
                -> Show err
                => Bool
                -> String
                -> ((y : a) -> Either err (type y))
                -> (x : a)
                -> IO (type x)
  timeToTryOrDie timing msg f a
      = do start <- clockTime UTC
           let r = f a
           case r of
             Left err => do stop <- clockTime UTC
                            putStrLn "Error Happened"
                            printLn err
                            let diff = timeDifference stop start
                            printLog timing diff msg
                            exitFailure
             Right res => do stop <- clockTime UTC
                             let diff =  timeDifference stop start
                             printLog timing diff msg
                             pure res
export
debug : Show a => Bool -> a -> IO ()
debug b e = when b (printLn e)

export
dump : Bool -> IO () -> IO ()
dump b e = when b e


export
Show (Run.ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines [ maybe "" show (location err)
                     , error err
                     ]
  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]


-- [ EOF ]
