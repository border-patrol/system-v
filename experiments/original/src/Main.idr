module Main

import System
import System.File
import System.Clock

import Toolkit.System

import SystemV
import SystemV.DSL

processArgs : List String -> IO $ Maybe (Bool, String)
processArgs (x::"--timing"::z::xs) = pure $ Just (True, z)
processArgs (x::y::xs) = pure $ Just (False, y)
processArgs _          = pure $ Nothing


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
  args <- getArgs
  Just (timing, fname) <- processArgs args | Nothing =>  putStrLn "Invalid args."
  (res) <- (parseSystemVDesignFile fname)
  case res of
    Left (FError err) => do {putStr "File Error: "; printLn err}
    Left (PError err) => do {putStrLn $ maybe "" show (location err); putStrLn (error err)}
    Left (LError (MkLexFail l i)) => do {print l; printLn i}
    Right ast => do
      putStrLn "LOG: Parsing Complete "


      (MkTerm u type term) <- timeToTryOrDie timing
                                             "LOG: Typing Complete "
                                             metaTypeCheck
                                             ast
      v <- timeToTryOrDie timing
                          "LOG: Evaluating "
                          eval
                          term

--      putStrLn "LOG : Pretty Printing"
--      let prettyMSV = prettySpec msv
--      printLn prettyMSV

      putStrLn "LOG : Bye"
