module SystemV.Base.Types.TYPE.Equiv

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Utilities
import SystemV.Base.Types.Direction

import SystemV.Base.Types.TYPE
import SystemV.Base.Types.TYPE.Equality

%default total

public export
data Error = NotEquiv (Equality.Error)
                      (TYPE (DATA TYPE))
                      (TYPE (DATA TYPE))

public export
data EquivTypes : (typeA, typeB : TYPE (DATA TYPE)) -> Type where
  Same : (prf : Equals Universe TYPE a b) -> EquivTypes a b

notEquiv : (Equals Universe TYPE a b -> Void)
        -> EquivTypes a b
        -> Void
notEquiv f (Same (Same Refl Refl)) = f (Same Refl Refl)

export
equivDataTypes : (a, b : TYPE (DATA TYPE))
                      -> DecInfo Equiv.Error (EquivTypes a b)
equivDataTypes a b with (DataTypes.decEq a b)
  equivDataTypes a b | (Yes prfWhy) with (prfWhy)
    equivDataTypes a a | (Yes prfWhy) | (Same Refl Refl) = Yes (Same prfWhy)
  equivDataTypes a b | (No msgWhyNot prfWhyNot) = No (NotEquiv msgWhyNot a b) (notEquiv prfWhyNot)

-- --------------------------------------------------------------------- [ EOF ]
