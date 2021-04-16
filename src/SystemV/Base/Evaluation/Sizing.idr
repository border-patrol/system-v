module SystemV.Base.Evaluation.Sizing

import SystemV.Common.Utilities
import SystemV.Base.Types
import SystemV.Base.Terms

import SystemV.Base.Evaluation.Values

%default total

public export
size : {n : Nat}
    -> (port : SystemV ctxt (PortTy (VectorTyDesc (W (S n) ItIsSucc) type) dir))
    -> (val  : Value port)
            -> SystemV ctxt (NatTy (S n))
size _ _ {n} = MkNat (S n)

-- [ EOF ]
