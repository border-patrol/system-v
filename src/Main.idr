module Main

import System
import System.File
import System.Clock

import Toolkit.System
import Toolkit.Options.ArgParse

import SystemV.Core
import SystemV.Core.DSL

record Opts where
  constructor MkOpts
  timing : Bool
  file   : List String

%inline
defOpts : Opts
defOpts = MkOpts False Nil

processArgs : List String -> IO Opts
processArgs args
    = case parseArgs defOpts convOpts args of
        Left err =>
          do printLn err
             exitFailure
        Right o => pure o

  where

    convOpts : Arg -> Opts -> Maybe Opts
    convOpts (File f)       o
      = Just (record {file $= (::)f} o)

    convOpts (KeyValue k v) o = Nothing

    convOpts (Flag x) o
      = case x of
          "timing"  => Just $ record {timing  = True} o
          otherwise => Nothing


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
  opts <- processArgs !getArgs
  case file opts of
    Nil =>
      do putStrLn "Error"
         exitFailure
    (a::_) =>
      do res <- parseSystemVDesignFile a
         case res of
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
