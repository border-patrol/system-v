module SystemV.Annotated.Pretty

import SystemV.Common.Run
import SystemV.Common.Options
import public SystemV.Common.Pretty

import SystemV.Annotated
import SystemV.Annotated.DSL


export
Show Evaluation.Annotated.Error where
  show NoFuel = "NoFuel"

Show Intention where
  show Data      = "Data"
  show Address   = "Address"
  show Clock     = "Clock"
  show Reset     = "Reset"
  show Info      = "Info"
  show Interrupt = "Interrupt"
  show Control   = "Control"
  show General   = "General"

Show Sensitivity where
  show High        = "High"
  show Low         = "Low"
  show Rising      = "Rising"
  show Falling     = "Falling"
  show Insensitive = "Insensitive"


Show (TYPE level) where
  show LogicTyDesc
    = "Logic"
  show LogicTy
    = "LogicVal"

  show (VectorTyDesc size type)
    = "Vect(" ++ show size ++ "," ++show type ++ ")"

  show (VectorTy size type)
    = "VectVal(" ++ show size ++ "," ++ show type ++ ")"

  show (FuncTy param return)
    = show param ++ " -> " ++ show return

  show ModuleTyDesc
    = "ModuleMeta"

  show ModuleTy
    = "Module"

  show (ChanTyDesc type s i)
    = "ChanMeta(" ++ show type ++ ","
                  ++ show s    ++ ","
                  ++ show i
                  ++ ")"
  show (ChanTy type s i)
    = "Chan(" ++ show type ++ ","
              ++ show s    ++ ","
              ++ show i
              ++ ")"

  show (PortTyDesc type dir s i)
    = "PortMeta(" ++ show type ++ ","
                  ++ show dir  ++ ","
                  ++ show s    ++ ","
                  ++ show i
                  ++ ")"

  show (PortTy type dir s i)
    = "Port(" ++ show type ++ ","
              ++ show dir  ++ ","
              ++ show s    ++ ","
              ++ show i
              ++ ")"

  show UnitTyDesc
    = "UnitMeta"
  show UnitTy
    = "Unit"

Show Cast.Direction.Error where
  show (CannotCast x y) = show x ++ " to " ++ show y


Show Equality.Error where
  show (KindMismatch x y) = "Kind mismatch"
  show (TypeMismatch x y)
    = trim $ unlines [ "Type Mismatch:"
                     , "Expected:"
                     , "\t" ++ show x
                     , "Given:"
                     , "\t" ++ show y]
  show (SensitivityMismatch x y)
    = trim $ unlines [ "Sensitivity Mismatch:"
                     , "Expected:"
                     , "\t" ++ show x
                     , "Given:"
                     , "\t" ++ show y]

  show (IntentionMismatch x y)
    = trim $ unlines [ "Intention Mismatch:"
                     , "Expected:"
                     , "\t" ++ show x
                     , "Given:"
                     , "\t" ++ show y]

Show Equiv.Error where
  show (NotEquiv x y z)
    = trim (unlines [ "Reason:"
                    , "\t" ++ show x
                    , "From:"
                    , "\t" ++ show y
                    , "To:"
                    , "\t" ++ show z])


Show Cast.Error where
  show (DirNotCast x)
    = "Cannot go from: " ++ show x
  show (TypesNotEquiv prf)
    = "Types are not equiv:\n" ++ show prf
  show (NotCastableFrom x)
    = "Cannot cast from: " ++ show x
  show (NotCastableTo x)
    = "Cannot cast to: " ++ show x

  show (SensitivityNotCompat err)
    = "Sensitivity not compatible"
  show (IntentionNotCompat err)
    = "Intention not compatible"

Show Argument.ValidType.Error where
  show IsData = "Is Data"
  show IsTerm = "Is Term"
  show IsFunc = "Is a Function"
  show IsModule = "Is a Module"
  show IsChan = "Is a Chan"

Show Synthesis.Error where
  show (NotValidArgumentType x)
    = "Not a valid function argument.\n" ++ show x

Show Argument.ValidTerm.Error where
  show IsData = "Is a data type"
  show IsType = "Is a type"
  show IsFunc = "Is a function"
  show IsModule = "Is a module"
  show IsChan = "Is a channel"

Show Return.ValidTerm.Error where
  show IsData = "Is a data type"
  show IsTerm = "Is a term"
  show IsChan = "Is a channel"
  show IsPort = "Is a port"
  show IsNat  = "Is a number"
  show (IsErrFunc x)
    = "Is a function:\n\t" ++ show x

Show Function.ValidTerm.Error where
  show (InvalidArgument x)
    = "Invalid argument type:\n" ++ show x

  show (InvalidReturn x)
    = "Invalid return type:\n" ++ show x

  show IsNotFunc = "Is not a function"
  show IsData    = "Is a data type"
  show IsType    = "Is a type"
  show IsModule  = "Is a module"
  show IsChan    = "Is a chan"
  show IsUnit    = "Is unit"
  show IsPort    = "Is a port"

export
Show Build.Annotated.Error where
  show (Err fc err) = trim (unlines [show fc, show err])

  show (NotAName a)
    = unwords ["NotAName", show a]

  show VectorSizeZero
    = "Vectors cannot have size zero."

  show (TypeMismatch x y)
    = trim $ unlines [ "Type Mismatch:"
                     , "Expected:"
                     , "\t" ++ show x
                     , "Given:"
                     , "\t" ++ show y
                     ]

  show (WrongType ctxt type) = "Wrong type"

  show (InvalidCast err from to)
    = trim (unlines [ "Invalid Cast"
                    , "Reason:"
                    , "\t" ++ show err
                    , "From:"
                    , "\t" ++ show from
                    , "To:"
                    , "\t" ++ show to
                    ])

  show (IndexOutOfBounds n w)
    = trim (unlines [ "Index Out of Bounds:"
                    , "Reason:"
                    , "\t" ++ show n
                    , "is not smaller than:"
                    , "\t" ++ show w
                    ])

  show (InvalidBound err)
    = "Invalid Bound " ++ show err

  show (InvalidFlow err)
    = "Invalid Flow\n" ++ show err

  show (InvalidFuncSynth err type)
    = trim (unlines [ "Invalid Synthesis"
                    , "Reason:"
                    , "\t" ++ show err
                    , "Type:"
                    , "\t" ++ show type
                    ])

  show (InvalidFunc err p r)
    = trim (unlines [ "Invalid Function"
                    , "Reason:"
                    , "\t" ++ show err
                    , "Argument:"
                    , "\t" ++ show p
                    , "Return:"
                    , "\t" ++ show r
                    ])



export
Show AST where
  show (Ref x)
    = (show . get) x

  show (Func fc name type body)
    = layout [ unwords ["(fun", show name, ":", show type, "->"]
             , unwords ["\t", show body]
              <+> ")"
             ]

  show (App x func param)
    = unwords ["(app", show func, show param <+> ")"]

  show (TyLogic fc) = "logic"
  show (TyVect fc s type)
    = show type <+> "[" <+> show s <+> "]"

  show (TyPort fc type dir s i )
    = unwords ["Port(", show type, show dir, show s, show i <+> ")"]

  show (MkChan fc type s i)
    = unwords ["(MkChan", show type, show s, show i <+> ")"]

  show (WriteTo fc chan)
    = unwords ["(writeTo", show chan <+> ")"]

  show (ReadFrom fc chan)
    = unwords ["(readFrom", show chan <+> ")"]

  show (Drive fc chan s i)
    = unwords ["(drive", show chan, show s, show i <+> ")"]

  show (Catch fc chan)
    = unwords ["(catch", show chan <+> ")"]

  show (Slice fc port s e)
    = unwords ["(Slice", show port, show (s,e),  ")"]

  show (IfThenElse fc test true false)
    = layout [unwords ["if (", show test <+> ")"]
             , "{"
             , unwords ["\t", show true]
             , "} else {"
             , unwords ["\t", show false]
             , "}"
             ]
  show (Connect fc portL portR)
    = unwords ["(connect", show portL, show portR <+> ")"]

  show (Cast fc port type dir s i)
    = unwords ["(cast", show port, show type, show dir, show s , show i <+> ")"]

  show (Let fc name value body)
    = layout [unwords ["let", show name, ":=", show value, "in"]
             , show body]

  show (Seq x y z)
    = layout [unwords [show y, ";"], show z ]

  show (EndModule x) = "endModule"
  show (UnitVal x) = "()"
  show (TyUnit x) = "()"

  show (NotGate x y z)
    = unwords ["(not", show y, show z <+> ")"]

  show (Gate x y z w v)
    = unwords ["(" <+> show y, show z, show w, show v <+> ")"]

  show (Index x y z)
    = unwords ["(index", show y, show z <+> ")"]



export
Show (SystemV ctxt type) where
  show TyUnit = "()"

  show TyModule = "module"
  show (TyChan typeD s i) = unwords ["Chan(", show typeD, show s , show i <+> ")"]
  show (TyPort desc dir s i)
    = unwords ["Port(", show desc, show dir, show s , show i <+> ")"]

  show TyLogic = "logic"
  show (TyVect size typeE)
    = show typeE <+> "[" <+> show size <+> "]"

  show (Var idx)
    = unwords ["(Var", show idx <+> ")"]

  show (Func x body chk prf)
    = layout [ unwords ["(fun", show x, "->"]
             , unwords ["\t", show body]
              <+> ")"
             ]

  show (App func value)
    = unwords ["(app", show func, show value <+> ")"]

  show MkUnit = "()"

  show EndModule = "endModule"

  show (MkPort type dir s i)
     = unwords ["(MkPort", show type, show dir, show s, show i <+> ")"]

  show (MkChan type s i)
     = unwords ["(MkChan", show type, show s, show i <+> ")"]

  show (WriteTo chan)
    = unwords ["(writeTo", show chan <+> ")"]

  show (ReadFrom  chan)
    = unwords ["(readFrom", show chan <+> ")"]

  show (Drive  chan s i)
    = unwords ["(drive", show chan, show s, show i <+> ")"]

  show (Catch chan)
    = unwords ["(catch", show chan <+> ")"]

  show (Slice port s e prf)
    = unwords ["(Slice", show port, show (s,e),  ")"]

  show (IfThenElseR test true false)
        = layout [unwords ["if (", show test <+> ")"]
             , "{"
             , unwords ["\t", show true]
             , "} else {"
             , unwords ["\t", show false]
             , "}"
             ]

  show (Connect portL portR prf)
    = unwords ["(connect", show portL, show portR <+> ")"]

  show (Cast port prf)
    = unwords ["(cast", show port, ")"]

  show (Index idx port prf)
    = unwords ["(index", show idx, show port <+> ")"]

  show (Not portO portI)
    = unwords ["(not", show portO, show portI <+> ")"]

  show (Gate kind portO portIA portIB)
     = unwords ["(" <+> show kind, show portO, show portIA, show portIB <+> ")"]

  show (Let value body)
      = layout [unwords ["let", show value, "in"]
             , show body]

  show (Seq left right)
    = layout [unwords [show left, ";"], show right ]


-- [ EOF ]
