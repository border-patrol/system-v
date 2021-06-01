module SystemV.HigherOrder.Terms.NormalForm.Error

%default total

namespace HigherOrder
  namespace NormalForm
    public export
    data Error = IsNotDataType
               | IsNotTermType
               | InvalidPortArgument
               | InvalidMkChan
               | InvalidGate

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
