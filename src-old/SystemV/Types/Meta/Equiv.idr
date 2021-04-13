module SystemV.Types.Meta.Equiv

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Utilities
import SystemV.Types.Direction
import SystemV.Types.Meta
import SystemV.Types.Meta.Equality

%default total

public export
data Error = NotEquiv (Equality.Error) (Meta (DATA TYPE)) (Meta (DATA TYPE))

public export
data EquivTypes : (typeA, typeB : Meta (DATA TYPE)) -> Type where
  Same : (prf : Equals Universe Meta a b) -> EquivTypes a b

notEquiv : (Equals Universe Meta a b -> Void)
        -> EquivTypes a b
        -> Void
notEquiv f (Same (Same Refl Refl)) = f (Same Refl Refl)

export
equivDataTypes : (a, b : Meta (DATA TYPE)) -> DecInfo Equiv.Error (EquivTypes a b)
equivDataTypes a b with (decEqTypesDataTypes a b)
  equivDataTypes a b | (Yes prfWhy) with (prfWhy)
    equivDataTypes a a | (Yes prfWhy) | (Same Refl Refl) = Yes (Same prfWhy)
  equivDataTypes a b | (No msgWhyNot prfWhyNot) = No (NotEquiv msgWhyNot a b) (notEquiv prfWhyNot)

-- --------------------------------------------------------------------- [ EOF ]
