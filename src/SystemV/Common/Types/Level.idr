module SystemV.Common.Types.Level

import Decidable.Equality

%default total
||| Levels at which types and their types are defined in our type
||| universes.
public export
data Level = TERM -- Describes a type that describes a value.
           | TYPE  -- Describes a type that describes a type.

valueNotType : TERM = TYPE -> Void
valueNotType Refl impossible

export
DecEq Level where
  decEq TERM TERM = Yes Refl
  decEq TERM TYPE = No valueNotType
  decEq TYPE TERM = No (negEqSym valueNotType)
  decEq TYPE TYPE = Yes Refl

-- [ EOF ]
