module SystemV.Param.Types.TYPE.Equality.Data

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE
import SystemV.Param.Types.TYPE.Equality.Error

import SystemV.Param.Types.TYPE.Equality.View
import SystemV.Param.Types.TYPE.Equality.DataTypes
import SystemV.Param.Types.TYPE.Equality.DataTerms

%default total

idxAreDiff : (DATA l = DATA l -> Void) -> Equals Universe TYPE a b -> Void
idxAreDiff f (Same prfIdx prfVal) = f Refl

diffTerms : (Equals Universe TYPE a b -> Void) -> Equals Universe TYPE a b -> Void
diffTerms f (Same prfIdx prfVal) = f (Same prfIdx prfVal)

diffTypes : (Equals Universe TYPE a b -> Void) -> Equals Universe TYPE a b -> Void
diffTypes f (Same prfIdx prfVal) = f (Same prfIdx prfVal)

export
decEq : {l : Level}
     -> (a : TYPE (DATA l))
     -> (b : TYPE (DATA l))
          -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq {l} a b with (byIndex a b)
  decEq {l = TERM} a b | (IdxSame a b Refl) with (DataTerms.decEq a b)
    decEq {l = TERM} a b | (IdxSame a b Refl) | (Yes prfWhy)
      = Yes prfWhy
    decEq {l = TERM} a b | (IdxSame a b Refl) | (No msgWhyNot prfWhyNot)
      = No msgWhyNot (diffTerms prfWhyNot)
  decEq {l = TYPE} a b | (IdxSame a b Refl) with (DataTypes.decEq a b)
    decEq {l = TYPE} a b | (IdxSame a b Refl) | (Yes prfWhy)
      = Yes prfWhy
    decEq {l = TYPE} a b | (IdxSame a b Refl) | (No msgWhyNot prfWhyNot)
      = No msgWhyNot (diffTypes prfWhyNot)

  decEq {l = l} a b | (IdxDiff a b prf) = No (TypeMismatch a b) (idxAreDiff prf)
