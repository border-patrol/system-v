module SystemV.Params.Pretty

import Data.List1

import SystemV.Common.Run
import SystemV.Common.Options

import public SystemV.Common.Pretty

import SystemV.Params
import SystemV.Params.DSL

Show (TYPE level) where
  show DATATYPE
    = "DATATYPE"

  show DATATERM
    = "DATATERM"

  show (FuncTy param return)
    = show param ++ " -> " ++ show return

  show (FuncParamTy u param return)
    = show param ++ " => " ++ show return

  show ModuleTyDesc
    = "ModuleMeta"

  show ModuleTy
    = "Module"

  show (ChanTyDesc)
    = "ChanMeta"
  show (ChanTy)
    = "Chan"

  show (PortTyDesc dir)
    = "PortMeta(" ++ show dir ++ ")"
  show (PortTy dir)
    = "Port(" ++ show dir ++ ")"

  show UnitTyDesc
    = "UnitMeta"
  show UnitTy
    = "Unit"

  show NatTyDesc
    = "NatMeta"
  show NatTy
    = "Nat"

  show BoolTyDesc
    = "BoolMeta"
  show BoolTy
    = "Bool"

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


Show Equiv.Error where
  show (NotEquiv x y z)
    = layout [ "Reason:"
             , "\t" ++ show x
             , "From:"
             , "\t" ++ show y
             , "To:"
             , "\t" ++ show z]


Show Cast.Error where
  show (DirNotCast x)
    = "Cannot go from: " ++ show x
  show (TypesNotEquiv prf)
    = "Types are not equiv:\n" ++ show prf

  show (NotCastableFrom x)
    = "Cannot cast from: " ++ show x
  show (NotCastableTo x)
    = "Cannot cast to: " ++ show x


Show Argument.ValidType.Error where
  show IsData = "Is Data"
  show IsTerm = "Is Term"
  show IsFunc = "Is a Function"
  show IsModule = "Is a Module"
  show IsChan = "Is a Chan"
  show IsNat = "Is a nat"
  show IsFuncParam = "Is a func param"
  show IsBool = "Is a bool"

Show Default.ValidType.Error where
  show IsDataTerm = "Is Data"
  show IsTerm = "Is Term"
  show IsFunc = "Is a Function"
  show IsModule = "Is a Module"
  show IsChan = "Is a Chan"
  show IsFuncParam = "Is a func param"
  show IsBool = "Is a bool"
  show IsData    = "Is a data type"
  show IsUnit    = "Is unit"
  show IsPort    = "Is a port"

Show Synthesis.Error where
  show (NotValidArgumentType x)
    = "Not a valid function argument.\n" ++ show x

Show Default.ValidTerm.Error where
  show IsData = "Is a data type"
  show IsType = "Is a type"
  show IsFunc = "Is a function"
  show IsModule = "Is a module"
  show IsChan = "Is a channel"
  show IsFuncParam = "Is a func param"
  show IsBool = "Is a bool"
  show IsPort = "Is a port"
  show IsUnit    = "Is unit"

Show Argument.ValidTerm.Error where
  show IsData = "Is a data type"
  show IsType = "Is a type"
  show IsFunc = "Is a function"
  show IsModule = "Is a module"
  show IsChan = "Is a channel"
  show IsNat = "Is a nat"
  show IsFuncParam = "Is a func param"
  show IsBool = "Is a bool"

Show Return.ValidTerm.Error where
  show IsData = "Is a data type"
  show IsTerm = "Is a term"
  show IsChan = "Is a channel"
  show IsPort = "Is a port"
  show IsNat  = "Is a number"
  show (IsErrFunc x)
    = "Is a function:\n\t" ++ show x
  show (IsErrFuncP e)
    = "Invalid function param def:\n" ++ show e

  show (IsErrFuncQ e)
    = "Invalid function return def:\n" ++ show e
  show IsBool = "Is a bool"

Show Function.ValidTerm.Error where
  show (InvalidArgument x)
    = "Invalid argument type:\n" ++ show x

  show (InvalidReturn x)
    = "Invalid return type:\n" ++ show x

  show (InvalidArgumentDef e)
    = "Invalid return def:\n" ++ show e

  show IsNotFunc = "Is not a function"
  show IsData    = "Is a data type"
  show IsType    = "Is a type"
  show IsModule  = "Is a module"
  show IsChan    = "Is a chan"
  show IsUnit    = "Is unit"
  show IsPort    = "Is a port"
  show IsNat = "Is a nat"
  show IsBool = "Is a bool"

Show ValidSeq.Error where
  show IsFunc = "Is a function"
  show IsFuncDef = "Is a function"
  show IsData    = "Is a data type"
  show IsType    = "Is a type"
  show IsModule  = "Is a module"
  show IsChan    = "Is a chan"
  show IsUnit    = "Is unit"
  show IsPort    = "Is a port"
  show IsNat     = "Is a nat"
  show IsBool    = "Is a bool"

Show ValidBind.Error where
  show IsType    = "Is a type"
  show IsUnit    = "Is unit"
  show IsPort    = "Is a port"
  show IsNat     = "Is a nat"
  show IsBool    = "Is a bool"

export
Show Build.Params.Error where
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
    = layout [ "Index Out of Bounds:"
             , "Reason:"
             , "\t" ++ show n
             , "is not smaller than:"
             , "\t" ++ show w
             ]

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
Show NormalForm.Error where
  show (Err fc err)
    = layout [ show fc
             , "Normal Form Error:"
             , "\t" ++ show err]

  show InvalidNat          = "Not a Nat"
  show InvalidBool         = "Not a Bool"
  show IsNotDataType       = "Is Not DataType"
  show IsNotTermType       = "Is Not TermType"
  show InvalidType         = "Is Not a Type"
  show InvalidPortArgument = "Invalid Port Argument"
  show InvalidDefaultArgument = "Invalid Default Argument"
  show InvalidMkChan       = "Invalid MkChan"
  show InvalidGate         = "Invalid Gate"
  show InvalidFor          = "Invalid For"
  show InvalidFunc         = "Invalid Func"
  show InvalidFuncBody     = "Invalid Func Body"
  show InvalidFuncLet      = "Invalid Func Let"
  show InvalidSeq          = "Invalid Seq"
  show InvalidConditional  = "Invalid Conditional"
  show InvalidApp          = "Invalid App"
  show InvalidDesignDecl   = "Invalid DesignDecl"
  show InvalidDesignBody   = "Invalid DesignBody"
  show InvalidDesignTop    = "Invalid DesignTop"


export
Show Params.Evaluation.Error where
  show (Err fc err)
    = layout [ show fc
             , "Runtime Error:"
             , "\t" ++ show err]

  show NoFuel = "NoFuel"
  show  VectorCannotBeZero     = "Vector cannot be zero"
  show  (IndexOutOfBounds n w) = "Index out of bounds"
  show  (InvalidCast err)      = "Invalid Cast"
  show  (InvalidBound err)     = "Invalid Range for Slize"
  show  (ArithOpError err)     = "Math Error"
  show  (TypeMismatch a b)     = "Type mismatch"
  show  ExpectedVector         = "Vector Expected"


export
Show Raw.AST where
  show (Ref x) = (show . get) x

  show (Func fc params ports body)
    = layout [ unwords ["(fun", show params, show ports, "->"]
             , unwords ["\t", show body]
              <+> ")"
             ]


  show (App fc func params ports)
    = unwords ["(app"
              , show func
              , maybe "[]" (show . forget) params
              , show ports <+> ")"]

  show (TyNat fc) = "nat"
  show (TyDATA fc) = "datatype"
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

  show (BExpr x y)
    = show y

  show (AExpr x y)
    = show y

  show (For x y z w)
    = layout [unwords ["for (", show y, ":=", show z <+> ")"]
             , "{"
             , unwords ["\t", show w]
             , "}"
             ]

  show (Size fc chan)
    = unwords ["(size", show chan <+> ")"]

export
Show Params.AST where
  show (Ref x)
    = (show . get) x

  show (Func fc name type body)
    = layout [ unwords ["(fun", show name, ":", show type, "->"]
             , unwords ["\t", show body]
              <+> ")"
             ]

  show (App x func param)
    = unwords ["(app", show func, show param <+> ")"]

  show (FuncDef fc name type def body)
    = layout [ unwords ["(fun", show name, ":", show type, "=", show def, "=>"]
             , unwords ["\t", show body]
              <+> ")"
             ]

  show (AppOver x func param)
    = unwords ["(appOver", show func, show param <+> ")"]


  show (AppDef x func)
    = unwords ["(appDef", show func <+> ")"]

  show (TyNat fc) = "nat"
  show (TyDATA fc) = "datatype"
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

  show (For x y z w)
    = layout [unwords ["for (", show y, ":=", show z <+> ")"]
             , "{"
             , unwords ["\t", show w]
             , "}"
             ]

  show (MkNat x k) = show k

  show (MkBool x y) = show y

  show (BoolNot x y)
    = unwords ["(not", show y <+> ")"]
  show (NatOpCmp x op l r)
    = unwords ["(" <+> show op, show l, show r <+> ")"]

  show (BoolOpBin x op l r)
    = unwords ["(" <+> show op, show l, show r <+> ")"]

  show (NatOpArith x op l r)
    = unwords ["(" <+> show op, show l, show r <+> ")"]

  show (Size fc chan)
    = unwords ["(size", show chan <+> ")"]

export
Show (SystemV ctxt type) where
  show (DATATYPE _) = "DATATYPE"
  show (TyUnit _) = "()"

  show (TyNat _) = "nat"
  show (TyBool _) = "bool"
  show (TyModule _) = "module"
  show (TyChan _ typeD) = unwords ["Chan(", show typeD <+> ")"]
  show (TyPort _ desc dir) = unwords ["Port(", show desc, show dir <+> ")"]
  show (TyLogic _) = "logic"
  show (TyVect fc size typeE)
    = show typeE <+> "[" <+> show size <+> "]"

  show (Var fc idx)
    = unwords ["(Var", show idx <+> ")"]

  show (Func cf x body chk prf)
    = layout [ unwords ["(fun", show x, "->"]
             , unwords ["\t", show body]
              <+> ")"
             ]

  show (App fc func value)
    = unwords ["(app", show func, show value <+> ")"]

  show (FuncParam fc x def body prf chk)
    = layout [ unwords ["(fun", show x, "=", show def, "=>"]
             , unwords ["\t", show body]
              <+> ")"
             ]

  show (AppDef fc  func)
    = unwords ["(appDef", show func <+> ")"]

  show (AppOver fc fun arg)
    = unwords ["(appOver", show fun, show arg <+> ")"]

  show (MkUnit fc) = "()"

  show (EndModule fc) = "endModule"

  show (MkPort fc type dir)
     = unwords ["(MkPort", show type, show dir <+> ")"]

  show (MkChan fc type)
     = unwords ["(MkChan", show type <+> ")"]

  show (WriteTo fc chan)
    = unwords ["(writeTo", show chan <+> ")"]

  show (ReadFrom fc  chan)
    = unwords ["(readFrom", show chan <+> ")"]

  show (Drive fc  chan)
    = unwords ["(drive", show chan <+> ")"]

  show (Catch fc chan)
    = unwords ["(catch", show chan <+> ")"]

  show (Slice fc port s e)
    = unwords ["(Slice", show port, show (s,e),  ")"]

  show (IfThenElseR fc test true false)
        = layout [unwords ["if (", show test <+> ")"]
             , "{"
             , unwords ["\t", show true]
             , "} else {"
             , unwords ["\t", show false]
             , "}"
             ]

  show (Connect c portL portR prf)
    = unwords ["(connect", show portL, show portR <+> ")"]

  show (Cast fc port t dir prf)
    = unwords ["(cast", show port, show t, show dir <+> ")"]

  show (Index fc idx port)
    = unwords ["(index", show idx, show port <+> ")"]

  show (Size fc port)
    = unwords ["(size", show port <+> ")"]

  show (Not fc portO portI)
    = unwords ["(not", show portO, show portI <+> ")"]

  show (Gate fc kind portO portIA portIB)
     = unwords ["(" <+> show kind, show portO, show portIA, show portIB <+> ")"]

  show (Let fc value body prf)
      = layout [unwords ["let", show value, "in"]
             , show body]

  show (Seq fc left right prf)
    = layout [unwords [show left, ";"], show right ]

  show (MkNat fc n) = show n
  show (MkBool fc b) = show b
  show (IfThenElseC fc test true false)
         = layout [unwords ["if (", show test <+> ")"]
             , "{"
             , unwords ["\t", show true]
             , "} else {"
             , unwords ["\t", show false]
             , "}"
             ]

  show (BoolNot fc y)
    = unwords ["(not", show y <+> ")"]
  show (NatOpCmp fc op l r)
    = unwords ["(" <+> show op, show l, show r <+> ")"]

  show (BoolOpBin fc op l r)
    = unwords ["(" <+> show op, show l, show r <+> ")"]

  show (NatOpArith fc op l r)
    = unwords ["(" <+> show op, show l, show r <+> ")"]

  show (For fc counter body)
    = layout [unwords ["for (", show counter <+> ")"]
             , "{"
             , unwords ["\t", show body]
             , "}"
             ]
-- [ EOF ]
