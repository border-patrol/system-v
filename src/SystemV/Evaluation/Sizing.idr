module SystemV.Evaluation.Sizing

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms

import SystemV.Evaluation.Values

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
