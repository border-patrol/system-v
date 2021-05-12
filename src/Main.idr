module Main

import System
import System.File
import System.Clock

import Data.List1

import Toolkit.System
import Toolkit.Options.ArgParse

import SystemV.Core
import SystemV.Core.DSL

import Options


%inline
printLog : Bool -> Clock type -> String -> IO ()
printLog True  t m = do putStr m
                        printLn t
printLog False t m = putStrLn m


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

main : IO ()
main = do
  Right opts <- processArgs
     | Left err => exitFailure

  case !(parseSystemVDesignFile ((head . files) opts)) of
    Left (FError err) =>
      do putStr "File Error: "
         printLn err
    Left (PError err) =>
      do putStrLn $ maybe "" show (location err)
         putStrLn (error err)
    Left (LError (MkLexFail l i)) =>
      do print l
         printLn i
    Right ast =>
      do putStrLn "LOG: Parsing Complete "
         term <- timeToTryOrDie (timing opts)
                                "LOG: Typing Complete "
                                isTerm
                                ast
         v <- timeToTryOrDie (timing opts)
                             "LOG: Evaluating "
                             eval
                             term

         putStrLn "LOG : Bye"
