module SystemV.HigherOrder.Terms.NormalForm

import SystemV.HigherOrder.Types
import SystemV.HigherOrder.Terms

import public SystemV.HigherOrder.Terms.NormalForm.Error
import public SystemV.HigherOrder.Terms.NormalForm.Types as NormalForm
import        SystemV.HigherOrder.Terms.NormalForm.Proofs

%default total

namespace HigherOrder
  public export
  data NF : (term : SystemV Nil type) -> Type where
    Design : Design.NF term -> HigherOrder.NF term

  export
  nf : (term : SystemV Nil ModuleTy)
            -> Either NormalForm.Error
                      (HigherOrder.NF term)
  nf term
    = do prf <- Design.nf term

         pure (Design prf)

-- [ EOF ]
