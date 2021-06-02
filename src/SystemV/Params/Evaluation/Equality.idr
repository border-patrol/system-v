module SystemV.Params.Evaluation.Equality

import Data.Vect

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values

%default total

namespace Data

  public export
  data DataEq : (a,b : SystemV Nil DATATERM) -> Type where
    LL : DataEq (TyLogic fcA)  (TyLogic fcB)
    VV : a = b
       -> DataEq typeA typeB
       -> DataEq (TyVect fcA (MkNat fcNA a) typeA) (TyVect fcB (MkNat fcNB b) typeB)

  logicNotVect : DataEq (TyLogic _) (TyVect _ _ _) -> Void
  logicNotVect LL impossible

  vectNotLogic : DataEq (TyVect _ _ _) (TyLogic _) -> Void
  vectNotLogic LL impossible

  sizeDiffer : (a = b -> Void)
            -> DataEq (TyVect _ (MkNat _ a) typeA) (TyVect _ (MkNat _ b) typeB) -> Void
  sizeDiffer contra (VV Refl x) = contra Refl

  innerDiffer : (DataEq typeA typeB -> Void) -> DataEq (TyVect _ (MkNat _ a) typeA) (TyVect _ (MkNat _ a) typeB) -> Void
  innerDiffer f (VV prf x) = f x

  export
  decEq : (a : SystemV Nil DATATERM)
       -> (Value a)
       -> (b : SystemV Nil DATATERM)
       -> (Value b)
       -> Dec (DataEq a b)
  decEq (TyLogic _) TyLogic (TyLogic _) TyLogic = Yes LL
  decEq (TyLogic _) TyLogic (TyVect _ _ _) (TyVect x y)
    = No logicNotVect

  decEq (TyVect _ _ _) (TyVect x z) (TyLogic _) TyLogic
    = No vectNotLogic

  decEq (TyVect _ (MkNat _ a) typeA) (TyVect x z) (TyVect _ (MkNat _ b) typeB) (TyVect y w) with (decEq a b)
    decEq (TyVect _ (MkNat _ a) typeA) (TyVect x z) (TyVect _ (MkNat _ a) typeB) (TyVect y w) | (Yes Refl) with (decEq typeA x typeB y)
      decEq (TyVect _ (MkNat _ a) typeA) (TyVect x z) (TyVect _ (MkNat _ a) typeB) (TyVect y w) | (Yes Refl) | (Yes prf)
        = Yes (VV Refl prf)
      decEq (TyVect _ (MkNat _ a) typeA) (TyVect x z) (TyVect _ (MkNat _ a) typeB) (TyVect y w) | (Yes Refl) | (No contra)
        = No (innerDiffer contra)


    decEq (TyVect _ (MkNat _ a) typeA) (TyVect x z) (TyVect _ (MkNat _ b) typeB) (TyVect y w) | (No contra)
      = No (sizeDiffer contra)

-- [ EOF ]
