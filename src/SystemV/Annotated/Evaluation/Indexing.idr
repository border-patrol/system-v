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
index i port prf val with (val)
  index i (MkPort ty dir sense intent) prf val | (MkPort x) with (x)
    index i (MkPort (TyVect s tyV) dir sense intent) prf val | (MkPort x) | (TyVect s z)
      = MkPort tyV dir sense intent

  index i (Seq left right) prf val | (Seq x y)
    = index i right prf y

-- [ EOF ]
