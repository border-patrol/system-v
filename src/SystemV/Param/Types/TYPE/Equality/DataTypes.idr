module SystemV.Param.Types.TYPE.Equality.DataTypes

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE
import SystemV.Param.Types.TYPE.Equality.Error


%default total


export
decEq : (a,b : TYPE (DATA TYPE))
            -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq DATATYPE DATATYPE = Yes (Same Refl Refl)

-- [ EOF ]
