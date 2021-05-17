module SystemV.Annotated.Evaluation.Slicing

import SystemV.Common.Utilities
import SystemV.Annotated.Types
import SystemV.Annotated.Terms

import SystemV.Annotated.Values

%default total

public export
slice : (a,o : Nat)
     -> (prf  : ValidBound a o s)
     -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir sense intent))
     -> (val  : Value port)
             -> SystemV ctxt (PortTy (VectorTyDesc (minus s o a prf) type) dir sense intent)
slice a o prf port val with (val)
  slice a o prf (MkPort ty dir sense intent) val | (MkPort x) with (x)
    slice a o prf (MkPort (TyVect s ty) dir sense intent) val | (MkPort x) | (TyVect s z)
      = MkPort (TyVect (minus s o a prf) ty) dir sense intent

  slice a o prf (Seq left right) val | (Seq x y)
    = Seq left (slice a o prf right y)

-- [ EOF ]
