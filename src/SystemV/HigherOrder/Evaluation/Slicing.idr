module SystemV.HigherOrder.Evaluation.Slicing

import SystemV.Common.Utilities
import SystemV.HigherOrder.Types
import SystemV.HigherOrder.Terms

import SystemV.HigherOrder.Values

%default total

public export
slice : (a,o : Nat)
     -> (prf  : ValidBound a o s)
     -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir))
     -> (val  : Value port)
             -> SystemV ctxt (PortTy (VectorTyDesc (minus s o a prf) type) dir)
slice a o prf (MkPort type dir) (MkPort x dir) with (x)
  slice a o prf (MkPort (TyVect s tyV) dir) (MkPort x dir) | (TyVect s z)
    = MkPort (TyVect (minus s o a prf) tyV) dir

slice _ _ _ (Seq _ _ IsUnit) (Seq _ _) impossible
slice _ _ _ (Seq _ _ IsMod) (Seq _ _) impossible

-- [ EOF ]
