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
slice a o prf (MkPort type dir sense intent) (MkPort x) with (x)
  slice a o prf (MkPort (TyVect s type) dir sense intent) (MkPort x) | (TyVect s z)
    = MkPort (TyVect (minus s o a prf) type) dir sense intent

slice _ _ _ (Seq _ _ IsUnit) (Seq _ _) impossible
slice _ _ _ (Seq _ _ IsMod) (Seq _ _) impossible

-- [ EOF ]
