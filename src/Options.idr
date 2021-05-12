module Options

import System

import Data.List1

import Toolkit.Options.ArgParse

%default total

data Error = MissingFile
           | ProcessError ArgParseError

public export
record Opts where
 constructor MkOpts
 timing : Bool
 files  : List1 String



record RawOpts where
  constructor MkRawOpts
  timing' : Bool
  files'  : List String

defOpts : RawOpts
defOpts = MkRawOpts False Nil

getRawOpts : List String -> Either Options.Error RawOpts
getRawOpts args
    = case parseArgs defOpts convOpts args of
        Left err => Left (ProcessError err)
        Right o => Right o

  where

    convOpts : Arg -> RawOpts -> Maybe RawOpts
    convOpts (File f)       o
      = Just (record {files' $= (::)f} o)

    convOpts (KeyValue k v) o = Nothing

    convOpts (Flag x) o
      = case x of
          "timing"  => Just $ record {timing'  = True} o
          otherwise => Nothing


processRawOpts : RawOpts -> Either Options.Error Opts
processRawOpts (MkRawOpts timing []) = Left MissingFile
processRawOpts (MkRawOpts timing (x :: xs)) = Right (MkOpts timing (x ::: xs))

export
processArgs : IO (Either Options.Error
                       Opts)
processArgs
  = case getRawOpts !getArgs of
      Left err => pure (Left err)
      Right o => pure (processRawOpts o)
