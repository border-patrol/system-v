module SystemV.Param.Evaluation.Equality

import Data.Vect

import SystemV.Common.Utilities
import SystemV.Param.Types
import SystemV.Param.Terms

import SystemV.Param.Evaluation.Values

%default total

namespace Data

  logicNotVect : TyLogic = TyVect (MkNat s) type -> Void
  logicNotVect Refl impossible


  export
  decEq : (a : SystemV Nil DATATERM)
       -> (Value a)
       -> (b : SystemV Nil DATATERM)
       -> (Value b)
       -> Dec (a === b)
  decEq TyLogic TyLogic TyLogic TyLogic = Yes Refl

  decEq TyLogic TyLogic (TyVect (MkNat s) type) (TyVect x y)
    = No logicNotVect


  decEq (TyVect (MkNat s) type) (TyVect x z) TyLogic TyLogic
    = No (negEqSym logicNotVect)

  decEq (TyVect (MkNat sA) tyA) (TyVect x z) (TyVect (MkNat sB) tyB) (TyVect y w) with (decEq sA sB)
    decEq (TyVect (MkNat sA) tyA) (TyVect x z) (TyVect (MkNat sA) tyB) (TyVect y w) | (Yes Refl) with (decEq tyA x tyB y)
      decEq (TyVect (MkNat sA) tyB) (TyVect x z) (TyVect (MkNat sA) tyB) (TyVect y w) | (Yes Refl) | (Yes Refl)
        = Yes Refl
      decEq (TyVect (MkNat sA) tyA) (TyVect x z) (TyVect (MkNat sA) tyB) (TyVect y w) | (Yes Refl) | (No contra)
        = No (\Refl => contra Refl)
    decEq (TyVect (MkNat sA) tyA) (TyVect x z) (TyVect (MkNat sB) tyB) (TyVect y w) | (No contra)
      = No (\Refl => contra Refl)
