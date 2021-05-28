module SystemV.Common.Options

import System

import Data.List1

import Toolkit.Options.ArgParse

%default total

data Error = MissingFile
           | ProcessError ArgParseError

export
Show Error where
  show MissingFile = "File expected"
  show (ProcessError err) = "Wrong args\n" ++ show err

public export
data Mode = CORE | ANNOTATED | HIGHERORDER | PARAM

public export
record Opts where
 constructor MkOpts
 timing : Bool
 files  : List1 String
 debug  : Bool



record RawOpts where
  constructor MkRawOpts
  timing' : Bool
  files'  : List String
  mode'   : Mode
  debug'  : Bool

defOpts : RawOpts
defOpts = MkRawOpts False Nil CORE False

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
          "timing"      => Just $ record {timing' = True} o
          "annotated"   => Just $ record {mode'   = ANNOTATED} o
          "core"        => Just $ record {mode'   = CORE} o
          "higherorder" => Just $ record {mode'   = HIGHERORDER} o
          "param"       => Just $ record {mode'   = PARAM} o
          "debug"       => Just $ record {debug'  = True} o
          otherwise => Nothing


processRawOpts : RawOpts -> Either Options.Error (Mode, Opts)
processRawOpts (MkRawOpts timing [] m b)
  = Left MissingFile
processRawOpts (MkRawOpts timing (x :: xs) m b)
  = Right (m, MkOpts timing (x ::: xs) b)

export
processArgs : IO (Either Options.Error
                         (Mode, Opts))
processArgs
  = case getRawOpts !getArgs of
      Left err => pure (Left err)
      Right o => pure (processRawOpts o)

export
getFirstFile : Opts -> String
getFirstFile = (head . files)
