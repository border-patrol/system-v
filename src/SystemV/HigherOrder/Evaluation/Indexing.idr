module SystemV.HigherOrder.Evaluation.Indexing

import SystemV.Common.Utilities
import SystemV.HigherOrder.Types
import SystemV.HigherOrder.Terms

import SystemV.HigherOrder.Values

%default total

public export
index : (i    : Nat)
     -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir))
     -> (prf  : LTE (S i) s)
     -> (val  : Value port)
             -> SystemV ctxt (PortTy type dir)
index i (MkPort type dir) prf (MkPort x dir) with (x)
  index i (MkPort (TyVect s tyV) dir) prf (MkPort x dir) | (TyVect s z)
    = MkPort tyV dir
index _ (Seq _ _ IsUnit) _ (Seq _ _) impossible
index _ (Seq _ _ IsMod) _ (Seq _ _) impossible

-- [ EOF ]
