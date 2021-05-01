module SystemV.Core.Types.TYPE.Equality.DataTerms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Core.Types.TYPE
import SystemV.Core.Types.TYPE.Equality.Error

%default total

logicTypeNotAVect : Equals Universe TYPE LogicTy (VectorTy n x) -> Void
logicTypeNotAVect (Same Refl Refl) impossible

vectTypeDiffSize : (contra : Not (n === m))
                -> (prf    : Equals Universe TYPE (VectorTy n x) (VectorTy m y))
                          -> Void
vectTypeDiffSize contra (Same Refl Refl) = contra Refl

vectTypeDiffType : (contra : Not (Equals Universe TYPE x y))
                -> (prf    : Equals Universe TYPE (VectorTy n x) (VectorTy n y))
                          -> Void
vectTypeDiffType contra (Same Refl Refl) = contra (Same Refl Refl)

export
decEq : (a,b : TYPE (DATA TERM))
            -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq a b with (a)

  decEq a b | LogicTy with (b)
    decEq a b | LogicTy | LogicTy = Yes (Same Refl Refl)
    decEq a b | LogicTy | (VectorTy n x) =  No (TypeMismatch a b) logicTypeNotAVect

  decEq a b | (VectorTy n x) with (b)
    decEq a b | (VectorTy n x) | LogicTy =  No (TypeMismatch a b) (negEqSym logicTypeNotAVect)
    decEq a b | (VectorTy n x) | (VectorTy k y) with (decEq n k)
      decEq a b | (VectorTy k x) | (VectorTy k y) | (Yes Refl) with (decEq x y)
        decEq a b | (VectorTy k x) | (VectorTy k y) | (Yes Refl) | (Yes prf) with (prf)
          decEq a b | (VectorTy k y) | (VectorTy k y) | (Yes Refl) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
        decEq a b | (VectorTy k x) | (VectorTy k y) | (Yes Refl) | (No msg contra) =  No msg (vectTypeDiffType contra)
      decEq a b | (VectorTy n x) | (VectorTy k y) | (No contra) =  No (TypeMismatch a b) (vectTypeDiffSize contra)
-- [ EOF ]
