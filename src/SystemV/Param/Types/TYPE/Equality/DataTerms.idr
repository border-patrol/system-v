module SystemV.Param.Types.TYPE.Equality.DataTerms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE
import SystemV.Param.Types.TYPE.Equality.Error

%default total

logicTypeNotAVect : Equals Universe TYPE LogicTy (VectorTy x) -> Void
logicTypeNotAVect (Same Refl Refl) impossible

vectTypeDiffType : (contra : Not (Equals Universe TYPE x y))
                -> (prf    : Equals Universe TYPE (VectorTy x) (VectorTy y))
                          -> Void
vectTypeDiffType contra (Same Refl Refl) = contra (Same Refl Refl)

export
decEq : (a,b : TYPE (DATA TERM))
            -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq a b with (a)
  decEq a b | LogicTy with (b)
    decEq a b | LogicTy | LogicTy = Yes (Same Refl Refl)
    decEq a b | LogicTy | (VectorTy x) =  No (TypeMismatch a b) logicTypeNotAVect

  decEq a b | (VectorTy x) with (b)
    decEq a b | (VectorTy x) | LogicTy =  No (TypeMismatch a b) (negEqSym logicTypeNotAVect)
    decEq a b | (VectorTy x) | (VectorTy y) with (decEq x y)
      decEq a b | (VectorTy x) | (VectorTy y) | (Yes prf) with (prf)
        decEq a b | (VectorTy y) | (VectorTy y) | (Yes prf) | (Same Refl Refl)
          = Yes (Same Refl Refl)
      decEq a b | (VectorTy x) | (VectorTy y) | (No msg contra)
        = No msg (vectTypeDiffType contra)

-- [ EOF ]
