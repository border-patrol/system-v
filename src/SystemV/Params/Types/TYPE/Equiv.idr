module SystemV.Params.Types.TYPE.Equiv

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Types.Direction

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality

%default total

public export
data Error = NotEquiv (Equality.Error)
                      (TYPE (DATA TERM))
                      (TYPE (DATA TERM))

public export
data EquivTypes : (typeA, typeB : TYPE (DATA TERM)) -> Type where
  Same : (prf : Equals Universe TYPE a b) -> EquivTypes a b

notEquiv : (Equals Universe TYPE a b -> Void)
        -> EquivTypes a b
        -> Void
notEquiv f (Same (Same Refl Refl)) = f (Same Refl Refl)

export
equivDataTypes : (a, b : TYPE (DATA TERM))
                      -> DecInfo Equiv.Error (EquivTypes a b)
equivDataTypes a b with (decEq a b)
  equivDataTypes a b | (Yes prfWhy) with (prfWhy)
    equivDataTypes a a | (Yes prfWhy) | (Same Refl Refl) = Yes (Same prfWhy)
  equivDataTypes a b | (No msgWhyNot prfWhyNot) = No (NotEquiv msgWhyNot a b) (notEquiv prfWhyNot)

-- --------------------------------------------------------------------- [ EOF ]
