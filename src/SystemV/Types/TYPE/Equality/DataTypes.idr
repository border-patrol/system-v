module SystemV.Types.TYPE.Equality.DataTypes

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Types.TYPE

import SystemV.Types.TYPE.Equality.Error


%default total

typeDefTyTypeNotEqual : (contra : Equals Universe TYPE x y -> Void)
                     -> (prf    : Equals Universe TYPE (TypeDefTy x) (TypeDefTy y))
                               -> Void
typeDefTyTypeNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

typeDefTyTypeNotABool : Equals Universe TYPE (TypeDefTy x) BoolTyDesc -> Void
typeDefTyTypeNotABool (Same Refl Refl) impossible

typeDefTyTypeNotALogic : Equals Universe TYPE (TypeDefTy x) LogicTyDesc -> Void
typeDefTyTypeNotALogic (Same Refl Refl) impossible

typeDefTyTypeNotAVect : Equals Universe TYPE (TypeDefTy x) (VectorTyDesc n y) -> Void
typeDefTyTypeNotAVect (Same Refl Refl) impossible

boolTypeNotALogic : Equals Universe TYPE BoolTyDesc LogicTyDesc -> Void
boolTypeNotALogic (Same Refl Refl) impossible

boolTypeNotAVect : Equals Universe TYPE BoolTyDesc (VectorTyDesc n x) -> Void
boolTypeNotAVect (Same Refl Refl) impossible

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
  decEq a b | (TypeDefTy x) with (b)
    decEq a b | (TypeDefTy x) | (TypeDefTy y) with (decEq x y)
      decEq a b | (TypeDefTy x) | (TypeDefTy y) | (Yes prf) with (prf)
        decEq a b | (TypeDefTy x) | (TypeDefTy x) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
      decEq a b | (TypeDefTy x) | (TypeDefTy y) | (No msg contra) =  No  msg (typeDefTyTypeNotEqual contra)

    decEq a b | (TypeDefTy x) | BoolTyDesc =  No (TypeMismatch a b) (typeDefTyTypeNotABool)

    decEq a b | (TypeDefTy x) | LogicTyDesc =  No (TypeMismatch a b) (typeDefTyTypeNotALogic)

    decEq a b | (TypeDefTy x) | (VectorTyDesc n y) =  No (TypeMismatch a b) (typeDefTyTypeNotAVect)

  decEq a b | BoolTyDesc with (b)
    decEq a b | BoolTyDesc | (TypeDefTy x) =  No (TypeMismatch a b) (negEqSym typeDefTyTypeNotABool)

    decEq a b | BoolTyDesc | BoolTyDesc = Yes (Same Refl Refl)
    decEq a b | BoolTyDesc | LogicTyDesc =  No (TypeMismatch a b) (boolTypeNotALogic)
    decEq a b | BoolTyDesc | (VectorTyDesc n x) =  No (TypeMismatch a b) (boolTypeNotAVect)

  decEq a b | LogicTyDesc with (b)
    decEq a b | LogicTyDesc | (TypeDefTy x) =  No (TypeMismatch a b) (negEqSym typeDefTyTypeNotALogic)
    decEq a b | LogicTyDesc | BoolTyDesc =  No (TypeMismatch a b) (negEqSym boolTypeNotALogic)
    decEq a b | LogicTyDesc | LogicTyDesc = Yes (Same Refl Refl)
    decEq a b | LogicTyDesc | (VectorTyDesc n x) =  No (TypeMismatch a b) logicTypeNotAVect

  decEq a b | (VectorTyDesc n x) with (b)
    decEq a b | (VectorTyDesc n x) | (TypeDefTy y) =  No (TypeMismatch a b) (negEqSym typeDefTyTypeNotAVect)
    decEq a b | (VectorTyDesc n x) | BoolTyDesc =  No (TypeMismatch a b) (negEqSym boolTypeNotAVect)
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
