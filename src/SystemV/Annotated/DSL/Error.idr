module SystemV.Annotated.DSL.Build.Error

import        Decidable.Equality

import        Data.Vect
import        Data.Nat
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem


import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import        SystemV.Common.Utilities

import        SystemV.Core.Types
import        SystemV.Core.Terms

namespace Build
  public export
  data NotDataTypeContext = InTypeDef | InVector | InPort | InChan

  public export
  data Context = NotADataType NotDataTypeContext
               | NotAChannel
               | NotAPort
               | NotAVect
               | NotAUnit
               | NotATerm
               | NotAType
               | NotAFunc
               | NotANat

  public export
  data Error = Err FileContext Build.Error
             | NotAName String
             | TypeMismatch (TYPE a) (TYPE b)
             | VectorSizeZero
             | IndexOutOfBounds Nat Whole
             | WrongType Context (TYPE a)
             | InvalidCast Cast.Error (TYPE (IDX TERM)) (TYPE (IDX TERM))
             | InvalidBound Sliceable.Error
             | InvalidFlow  Flow.Error
             | InvalidFuncSynth Synthesis.Error (TYPE a)
             | InvalidFunc Function.ValidTerm.Error (TYPE a) (TYPE b)

Show Direction where
  show IN = "IN"
  show OUT = "OUT"
  show INOUT = "INOUT"


Show Sliceable.Error where
  show (BadBound k j) = "Bad Bound: " ++ "(" ++ show k ++ "," ++ show j ++ ")"
  show (IndexStartsZero k) = "Index must start at zero " ++ show k
  show (IndexToBig k) = "Index to Big " ++ show k


Show Whole where
  show (W n prf) = show n


Show (TYPE level) where
  show LogicTyDesc
    = "Logic"
  show LogicTy
    = "LogicVal"

  show (VectorTyDesc size type)
    = "Vect(" ++ show size ++ show type ++ ")"

  show (VectorTy size type)
    = "VectVal(" ++ show size ++ "," ++ show type ++ ")"

  show (FuncTy param return)
    = show param ++ " -> " ++ show return

  show ModuleTyDesc
    = "ModuleMeta"

  show ModuleTy
    = "Module"

  show (ChanTyDesc type)
    = "ChanMeta(" ++ show type ++ ")"
  show (ChanTy type)
    = "Chan(" ++ show type ++ ")"

  show (PortTyDesc type dir)
    = "PortMeta(" ++ show type ++ ", " ++ show dir ++ ")"
  show (PortTy type dir)
    = "Port(" ++ show type ++ ", " ++ show dir ++ ")"

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

Show Flow.Error where
 show (CannotFlow x y)
   = "Cannot flow between: " ++ show x ++ " & " ++ show y

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
Show Build.Error where
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
