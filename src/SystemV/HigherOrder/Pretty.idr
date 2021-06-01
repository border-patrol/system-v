module SystemV.HigherOrder.Pretty

import SystemV.Common.Run
import SystemV.Common.Options

import public SystemV.Common.Pretty

import SystemV.Core.Pretty

import SystemV.HigherOrder
import SystemV.HigherOrder.DSL

import SystemV.HigherOrder.Types.Synthesis

export
Show Evaluation.HigherOrder.Error where
  show NoFuel = "NoFuel"

export
Show HigherOrder.NormalForm.Error where
  show IsNotDataType       = "NF Error:\n\t Is Not DataType"
  show IsNotTermType       = "NF Error:\n\t Is Not TermType"
  show InvalidPortArgument = "NF Error:\n\t Invalid Port Argument"
  show InvalidMkChan       = "NF Error:\n\t Invalid MkChan"
  show InvalidGate         = "NF Error:\n\t Invalid Gate"
  show InvalidFunc         = "NF Error:\n\t Invalid Func"
  show InvalidFuncBody     = "NF Error:\n\t Invalid Func Body"
  show InvalidFuncLet      = "NF Error:\n\t Invalid Func Let"
  show InvalidSeq          = "NF Error:\n\t Invalid Seq"
  show InvalidConditional  = "NF Error:\n\t Invalid Conditional"
  show InvalidApp          = "NF Error:\n\t Invalid App"
  show InvalidDesignDecl   = "NF Error:\n\t Invalid DesignDecl"
  show InvalidDesignBody   = "NF Error:\n\t Invalid DesignBody"
  show InvalidDesignTop    = "NF Error:\n\t Invalid DesignTop"


mutual
  Show Function.Type.Error where
    show (InvalidArgument x)
      = "Invalid argument type:\n" ++ show x

    show (InvalidReturn x)
      = "Invalid return type:\n" ++ show x

    show IsData    = "Is a data type"
    show IsTerm    = "Is a term"
    show IsModule  = "Is a module"
    show IsChan    = "Is a chan"
    show IsUnit    = "Is unit"
    show IsPort    = "Is a port"

  Show Returned.Type.Error where
    show IsData = "Is a data type"
    show IsTerm = "Is a term"
    show IsChan = "Is a channel"
    show IsPort = "Is a port"
    show IsNat  = "Is a number"
    show IsUnit = "Is Unit"
    show (IsErrFunc x)
      = "Is a function:\n\t" ++ show x

  Show Argument.Type.Error where
    show IsData = "Is Data"
    show IsTerm = "Is Term"
    show IsModule = "Is a Module"
    show IsChan = "Is a Chan"
    show (IsErrFunc x)
      = "Is a function:\n\t" ++ show x

  Show Synthesis.Argument.Error where
    show (NotValidArgumentType x)
      = "Not a valid function argument.\n" ++ show x


  Show Argument.Term.Error where
    show IsData = "Is a data type"
    show IsType = "Is a type"
    show IsModule = "Is a module"
    show IsChan = "Is a channel"
    show (IsErrFunc x)
      = "Is a function:\n\t" ++ show x

  Show Returned.Term.Error where
    show IsData = "Is a data type"
    show IsType = "Is a term"
    show IsChan = "Is a channel"
    show IsPort = "Is a port"
    show IsNat  = "Is a number"
    show IsUnit = "Is Unit"
    show (IsErrFunc x)
      = "Is a function:\n\t" ++ show x

  Show Function.Term.Error where
    show (InvalidArgument x)
      = "Invalid argument type:\n" ++ show x

    show (InvalidReturn x)
      = "Invalid return type:\n" ++ show x

    show IsData    = "Is a data type"
    show IsType    = "Is a type"
    show IsModule  = "Is a module"
    show IsChan    = "Is a chan"
    show IsUnit    = "Is unit"
    show IsPort    = "Is a port"

export
Show Build.HigherOrder.Error where
  show (Err fc err) = layout [show fc, show err]

  show (NotAName a)
    = unwords ["NotAName", show a]

  show VectorSizeZero
    = "Vectors cannot have size zero."

  show (TypeMismatch x y)
    = layout [ "Type Mismatch:"
             , "Expected:"
             , "\t" ++ show x
             , "Given:"
             , "\t" ++ show y
             ]

  show (WrongType ctxt type) = "Wrong type"

  show (InvalidCast err from to)
    = layout [ "Invalid Cast"
             , "Reason:"
             , "\t" ++ show err
             , "From:"
             , "\t" ++ show from
             , "To:"
             , "\t" ++ show to
             ]

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
    = layout [ "Invalid Synthesis"
             , "Reason:"
             , "\t" ++ show err
             , "Type:"
             , "\t" ++ show type
             ]

  show (InvalidFunc err p r)
    = layout [ "Invalid Function"
             , "Reason:"
             , "\t" ++ show err
             , "Argument:"
             , "\t" ++ show p
             , "Return:"
             , "\t" ++ show r
             ]

  show (InvalidSeq err)
    = layout [ "Invalid Sequencing"
             , "Reason:"
             , "\t" ++ show err
             ]

  show (InvalidBind err)
    = layout [ "Invalid Bind"
             , "Reason:"
             , "\t" ++ show err
             ]

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

  show (TyModule fc) = "module"

  show (TyFunc fc n p r) =
    unwords ["("<+> n, ":", show p, "->", show r <+> ")"]

  show (TyLogic fc) = "logic"
  show (TyVect fc s type)
    = show type <+> "[" <+> show s <+> "]"

  show (TyPort fc type dir)
    = unwords ["Port(", show type, show dir <+> ")"]

  show (MkChan fc type)
    = unwords ["(MkChan", show type <+> ")"]

  show (WriteTo fc chan)
    = unwords ["(writeTo", show chan <+> ")"]

  show (ReadFrom fc chan)
    = unwords ["(readFrom", show chan <+> ")"]

  show (Drive fc chan)
    = unwords ["(drive", show chan <+> ")"]

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

  show (Cast fc port type dir)
    = unwords ["(cast", show port, show type, show dir <+> ")"]

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
  show (TyFunc p r _) =
    unwords ["(" <+> show p, "->", show r <+> ")"]

  show TyModule = "module"
  show (TyChan typeD) = unwords ["Chan(", show typeD <+> ")"]
  show (TyPort desc dir)
    = unwords ["Port(", show desc, show dir <+> ")"]

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

  show (MkPort type dir)
     = unwords ["(MkPort", show type, show dir<+> ")"]

  show (MkChan type)
     = unwords ["(MkChan", show type <+> ")"]

  show (WriteTo chan)
    = unwords ["(writeTo", show chan <+> ")"]

  show (ReadFrom  chan)
    = unwords ["(readFrom", show chan <+> ")"]

  show (Drive chan)
    = unwords ["(drive", show chan <+> ")"]

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

  show (Let value body prf)
      = layout [unwords ["let", show value, "in"]
             , show body]

  show (Seq left right prf)
    = layout [unwords [show left, ";"], show right ]


-- [ EOF ]
