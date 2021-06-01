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
    App : Design.Body.NF term -> Core.NF (App term MkUnit)

  export
  nf : (term : SystemV Nil ModuleTy)
            -> Either NormalForm.Error
                      (Core.NF term)
  nf (App func MkUnit)
    = do prf <- Design.Body.nf func

         pure (App prf)

  nf _ = Left InvalidDesignTop


-- [ EOF ]
