module SystemV.Params.Types.TYPE.Equality.DataTerms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality.Error

%default total

export
decEq : (a,b : TYPE (DATA TERM))
            -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq DATATERM DATATERM = Yes (Same Refl Refl)


-- [ EOF ]
