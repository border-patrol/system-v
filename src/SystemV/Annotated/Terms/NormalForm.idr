module SystemV.Annotated.Terms.NormalForm

import SystemV.Annotated.Types
import SystemV.Annotated.Terms

import public SystemV.Annotated.Terms.NormalForm.Error
import public SystemV.Annotated.Terms.NormalForm.Types as NormalForm
import        SystemV.Annotated.Terms.NormalForm.Proofs

%default total

namespace Annotated
  public export
  data NF : (term : SystemV Nil type) -> Type where
    Design : Design.NF term -> Annotated.NF term

  export
  nf : (term : SystemV Nil ModuleTy)
            -> Either NormalForm.Error
                      (Annotated.NF term)
  nf term
    = do prf <- Design.nf term

         pure (Design prf)

-- [ EOF ]
