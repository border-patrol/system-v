module SystemV.Core.Terms.NormalForm

import SystemV.Core.Types
import SystemV.Core.Terms

import public SystemV.Core.Terms.NormalForm.Error
import public SystemV.Core.Terms.NormalForm.Types as NormalForm
import        SystemV.Core.Terms.NormalForm.Proofs

%default total

namespace Core
  public export
  data NF : (term : SystemV Nil type) -> Type where
    Design : Design.NF term -> Core.NF term

  export
  nf : (term : SystemV Nil ModuleTy)
            -> Either NormalForm.Error
                      (Core.NF term)
  nf term
    = do prf <- Design.nf term

         pure (Design prf)

-- [ EOF ]
