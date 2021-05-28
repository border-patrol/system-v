module SystemV.Param.DSL.Error

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

import        SystemV.Param.Types
import        SystemV.Param.Terms

import SystemV.Param.Types.TYPE.Function.Synthesis

namespace Build
  public export
  data NotDataTypeContext = InTypeDef | InVector | InPort | InChan | InCast | InFunc

  public export
  data Context = NotADataType NotDataTypeContext
               | NotAChannel
               | NotAPort
               | NotAVect
               | NotAUnit
               | NotATerm
               | NotAType
               | NotAFunc
               | NotAFuncDef
               | NotANat
               | NotABool

  namespace Param
    public export
    data Error = Err FileContext Param.Error
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

-- [ EOF ]
