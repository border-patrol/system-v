module SystemV.Base.Evaluation.Sizing

import SystemV.Common.Utilities
import SystemV.Base.Types
import SystemV.Base.Terms

import SystemV.Base.Evaluation.Values

%default total

public export
size : (port : SystemV ctxt (PortTy (VectorTyDesc (W (S n) ItIsSucc) type) dir))
    -> (val  : Value port)
            -> SystemV ctxt (NatTy (S n))
size port val {n} with (val)
  size (MkPort ty dir) val {n} | (MkPort tyV dir)
    = MkNat (S n)
  size (Seq left right) val {n} | (Seq x y)
    = size right y

-- [ EOF ]
