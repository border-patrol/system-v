module SystemV.Params.Evaluation.Slicing

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values

%default total

public export
slice : FC
     -> (a,o,s : Nat)
     -> (prfW  : IsSucc s)
     -> (prf  : ValidBound a o (W s prfW))
     -> (ty   : SystemV ctxt DATATERM)
     -> (dir  : Direction)
             -> SystemV ctxt (PortTy dir)
slice fc a o s prfW prf ty dir with (minus (W s prfW) o a prf)
  slice fc a o s prfW prf ty dir | (W (S n) ItIsSucc)
    = MkPort fc (TyVect fc (MkNat fc (S n)) ty) dir

-- [ EOF ]
