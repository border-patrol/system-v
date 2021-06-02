module SystemV.Params.Terms.NormalForm

import SystemV.Params.Types
import SystemV.Params.Terms

import public SystemV.Params.Terms.NormalForm.Error
import public SystemV.Params.Terms.NormalForm.Types as NormalForm
import        SystemV.Params.Terms.NormalForm.Proofs

%default total

namespace Params
  public export
  data NF : (term : SystemV Nil type) -> Type where
    Design : Design.NF term -> Params.NF term

  export
  nf : (term : SystemV Nil ModuleTy)
            -> Either NormalForm.Error
                      (Params.NF term)
  nf term
    = do prf <- Design.nf term

         pure (Design prf)

-- [ EOF ]
