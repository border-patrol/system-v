module SystemV.HigherOrder.DSL.Error

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

import        SystemV.HigherOrder.Types
import        SystemV.HigherOrder.Terms
import        SystemV.HigherOrder.Types.Function
import        SystemV.HigherOrder.Types.Synthesis

namespace Build
  public export
  data NotDataTypeContext = InTypeDef | InVector | InPort | InChan | InCast

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

  namespace HigherOrder
    public export
    data Error = Err FileContext HigherOrder.Error
               | NotAName String
               | TypeMismatch (TYPE a) (TYPE b)
               | VectorSizeZero
               | IndexOutOfBounds Nat Whole
               | WrongType Context (TYPE a)
               | InvalidCast Cast.Error (TYPE (IDX TERM)) (TYPE (IDX TERM))
               | InvalidBound Sliceable.Error
               | InvalidFlow  Flow.Error
               | InvalidFuncSynth Synthesis.Argument.Error (TYPE a)
               | InvalidFunc Function.Term.Error (TYPE a) (TYPE b)
               | InvalidSeq ValidSeq.Error
               | InvalidBind ValidBind.Error

-- [ EOF ]
