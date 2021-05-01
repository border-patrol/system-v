module SystemV.Core.Evaluation.Slicing

import SystemV.Common.Utilities
import SystemV.Core.Types
import SystemV.Core.Terms

import SystemV.Core.Evaluation.Values

%default total

public export
slice : (a,o : Nat)
     -> (prf  : ValidBound a o s)
     -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir))
     -> (val  : Value port)
             -> SystemV ctxt (PortTy (VectorTyDesc (minus s o a prf) type) dir)
slice a o prf port val with (val)
  slice a o prf (MkPort ty dir) val | (MkPort x dir) with (x)
    slice a o prf (MkPort (TyVect s ty) dir) val | (MkPort x dir) | (TyVect s z)
      = MkPort (TyVect (minus s o a prf) ty) dir

  slice a o prf (Seq left right) val | (Seq x y)
    = Seq left (slice a o prf right y)

-- [ EOF ]
