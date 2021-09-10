module SystemV.Core.DSL.Error

import        Decidable.Equality

import        Data.Vect
import        Data.Nat
import        Data.List
import        Data.List.Views
import        Data.String
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

  namespace Core
    public export
    data Error = Err FileContext Core.Error
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
               | InvalidSeq ValidSeq.Error
               | InvalidBind ValidBind.Error

-- [ EOF ]
