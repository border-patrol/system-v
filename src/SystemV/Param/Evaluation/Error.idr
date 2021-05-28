module SystemV.Param.Evaluation.Error

import SystemV.Param.Types
import SystemV.Param.Terms

%default total

namespace Param.Evaluation
  public export
  data Error = VectorCannotBeZero
             | IndexOutOfBounds Nat Whole
             | InvalidCast Cast.Error
             | InvalidBound Sliceable.Error
             | UnexpectedSeq
             | ArithOpError Arithmetic.Error
             | TypeMismatch (SystemV Nil DATATERM) (SystemV Nil DATATERM)
             | ExpectedVector
             | NoFuel

-- [ EOF ]
