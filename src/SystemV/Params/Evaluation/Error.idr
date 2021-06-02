module SystemV.Params.Evaluation.Error

import SystemV.Params.Types
import SystemV.Params.Terms

%default total

namespace Params.Evaluation
  public export
  data Error = Err FileContext Params.Evaluation.Error
             | VectorCannotBeZero
             | IndexOutOfBounds Nat Whole
             | InvalidCast Cast.Error
             | InvalidBound Sliceable.Error
             | ArithOpError Arithmetic.Error
             | TypeMismatch (SystemV Nil DATATERM) (SystemV Nil DATATERM)
             | ExpectedVector
             | NoFuel

-- [ EOF ]
