module SystemV.Param.Evaluation.Slicing

import SystemV.Common.Utilities

import SystemV.Param.Types
import SystemV.Param.Terms

import SystemV.Param.Evaluation.Values

%default total

public export
slice : (a,o,s : Nat)
     -> (prfW  : IsSucc s)
     -> (prf  : ValidBound a o (W s prfW))
     -> {type : TYPE (DATA TERM)}
     -> (ty   : SystemV ctxt type)
     -> (dir  : Direction)
             -> SystemV ctxt (PortTy (VectorTy type) dir)
slice a o s prfW prf ty dir with (minus (W s prfW) o a prf)
  slice a o s prfW prf ty dir | (W (S n) ItIsSucc)
    = MkPort (TyVect (MkNat (S n)) ty) dir

-- [ EOF ]