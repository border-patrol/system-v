module SystemV.Param.Types.TYPE.Equality.DataTypes

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE
import SystemV.Param.Types.TYPE.Equality.Error


%default total

--logicTypeNotAVect : Equals Universe TYPE LogicTyDesc (VectorTyDesc x) -> Void
--logicTypeNotAVect (Same Refl Refl) impossible
--
--vectTypeDiffType : (contra : Not (Equals Universe TYPE x y))
--                -> (prf    : Equals Universe TYPE (VectorTyDesc x) (VectorTyDesc y))
--                          -> Void
--vectTypeDiffType contra (Same Refl Refl) = contra (Same Refl Refl)

export
decEq : (a,b : TYPE (DATA TYPE))
            -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq DATATYPE DATATYPE = Yes (Same Refl Refl)

--decEq a b with (a)
--  decEq a b | LogicTyDesc with (b)
--    decEq a b | LogicTyDesc | LogicTyDesc = Yes (Same Refl Refl)
--    decEq a b | LogicTyDesc | (VectorTyDesc x) =  No (TypeMismatch a b) logicTypeNotAVect
--
--  decEq a b | (VectorTyDesc x) with (b)
--    decEq a b | (VectorTyDesc x) | LogicTyDesc =  No (TypeMismatch a b) (negEqSym logicTypeNotAVect)
--    decEq a b | (VectorTyDesc x) | (VectorTyDesc y) with (decEq x y)
--      decEq a b | (VectorTyDesc x) | (VectorTyDesc y) | (Yes prfWhy) with (prfWhy)
--        decEq a b | (VectorTyDesc y) | (VectorTyDesc y) | (Yes prfWhy) | (Same Refl Refl)
--          = Yes (Same Refl Refl)
--
--      decEq a b | (VectorTyDesc x) | (VectorTyDesc y) | (No msgWhyNot prfWhyNot)
--        = No msgWhyNot (vectTypeDiffType prfWhyNot)

-- [ EOF ]
