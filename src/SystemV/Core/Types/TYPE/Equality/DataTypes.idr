module SystemV.Core.Types.TYPE.Equality.DataTypes

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Core.Types.TYPE
import SystemV.Core.Types.TYPE.Equality.Error

%default total


logicTypeNotAVect : Equals Universe TYPE LogicTyDesc (VectorTyDesc n x) -> Void
logicTypeNotAVect (Same Refl Refl) impossible

vectTypeDiffSize : (contra : Not (n === m))
                -> (prf    : Equals Universe TYPE (VectorTyDesc n x) (VectorTyDesc m y))
                          -> Void
vectTypeDiffSize contra (Same Refl Refl) = contra Refl

vectTypeDiffType : (contra : Not (Equals Universe TYPE x y))
                -> (prf    : Equals Universe TYPE (VectorTyDesc n x) (VectorTyDesc n y))
                          -> Void
vectTypeDiffType contra (Same Refl Refl) = contra (Same Refl Refl)

export
decEq : (a,b : TYPE (DATA TYPE))
            -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq a b with (a)

  decEq a b | LogicTyDesc with (b)
    decEq a b | LogicTyDesc | LogicTyDesc = Yes (Same Refl Refl)
    decEq a b | LogicTyDesc | (VectorTyDesc n x) =  No (TypeMismatch a b) logicTypeNotAVect

  decEq a b | (VectorTyDesc n x) with (b)
    decEq a b | (VectorTyDesc n x) | LogicTyDesc =  No (TypeMismatch a b) (negEqSym logicTypeNotAVect)
    decEq a b | (VectorTyDesc n x) | (VectorTyDesc k y) with (decEq n k)
      decEq a b | (VectorTyDesc k x) | (VectorTyDesc k y) | (Yes Refl) with (decEq x y)
        decEq a b | (VectorTyDesc k x) | (VectorTyDesc k y) | (Yes Refl) | (Yes prfWhy) with (prfWhy)
          decEq a b | (VectorTyDesc k y) | (VectorTyDesc k y) | (Yes Refl) | (Yes prfWhy) | (Same Refl Refl)
            = Yes (Same Refl Refl)

        decEq a b | (VectorTyDesc k x) | (VectorTyDesc k y) | (Yes Refl) | (No msgWhyNot prfWhyNot)
          = No msgWhyNot (vectTypeDiffType prfWhyNot)

      decEq a b | (VectorTyDesc n x) | (VectorTyDesc k y) | (No contra)
        = No (TypeMismatch a b) (vectTypeDiffSize contra)

-- [ EOF ]
