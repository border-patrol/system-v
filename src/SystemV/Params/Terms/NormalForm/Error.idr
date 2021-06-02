module SystemV.Params.Terms.NormalForm.Error

import Toolkit.Data.Location

%default total

namespace NormalForm
  public export
  data Error = Err FileContext NormalForm.Error
             | InvalidNat
             | InvalidBool
             | IsNotDataType
             | IsNotTermType
             | InvalidType
             | InvalidPortArgument
             | InvalidDefaultArgument
             | InvalidMkChan
             | InvalidGate
             | InvalidFor

             | InvalidFunc
             | InvalidFuncBody
             | InvalidFuncLet
             | InvalidSeq
             | InvalidConditional
             | InvalidApp

             | InvalidDesignDecl
             | InvalidDesignBody
             | InvalidDesignTop

-- [ EOF ]
