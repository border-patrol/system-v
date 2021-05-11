module SystemV.Param.Evaluation.Sizing

import SystemV.Common.Utilities

import SystemV.Param.Types
import SystemV.Param.Terms

import SystemV.Param.Evaluation.Values

public export
size : (vec : SystemV Nil (VectorTy type))
    -> (val : Value vec)
           -> SystemV Nil NatTy
size vec val with (val)
  size (TyVect (MkNat s) ty) val | (TyVect x y) = MkNat s

-- [ EOF ]
