module SystemV.Base.Evaluation.Indexing

import SystemV.Common.Utilities
import SystemV.Base.Types
import SystemV.Base.Terms

import SystemV.Base.Evaluation.Values

%default total

public export
index : (i    : Nat)
     -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir))
     -> (prf  : LTE (S i) s)
     -> (val  : Value port)
             -> SystemV ctxt (PortTy type dir)
index i port prf val with (val)
  index i (MkPort ty dir) prf val | (MkPort x dir) with (x)
    index i (MkPort (TyVect s tyV) dir) prf val | (MkPort x dir) | (TyVect s z)
      = MkPort tyV dir

  index i (Seq left right) prf val | (Seq x y)
    = index i right prf y

-- [ EOF ]
