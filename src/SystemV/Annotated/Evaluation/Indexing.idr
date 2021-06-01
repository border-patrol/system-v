module SystemV.Annotated.Evaluation.Indexing

import SystemV.Common.Utilities
import SystemV.Annotated.Types
import SystemV.Annotated.Terms

import SystemV.Annotated.Values

%default total

public export
index : (i    : Nat)
     -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir sense intent))
     -> (prf  : LTE (S i) s)
     -> (val  : Value port)
             -> SystemV ctxt (PortTy type dir sense intent)
index i (MkPort type dir sense intent) prf (MkPort x) with (x)
  index i (MkPort (TyVect s type) dir sense intent) prf (MkPort x) | (TyVect s z)
    = MkPort type dir sense intent

index _ (Seq _ _ IsUnit) _ (Seq _ _) impossible
index _ (Seq _ _ IsMod) _ (Seq _ _) impossible

-- [ EOF ]
