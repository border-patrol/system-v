module SystemV.Common.Types.Nat.Comparison

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

%hide Data.Nat.LT
%hide Prelude.LT
%hide Data.Nat.GT
%hide Prelude.GT

public export
data CompOp = EQ
            | LT
            | GT

eqNotLT : EQ = LT -> Void
eqNotLT Refl impossible

eqNotGT : EQ = GT -> Void
eqNotGT Refl impossible

ltNotGT : LT = GT -> Void
ltNotGT Refl impossible

export
decEq : (a,b : CompOp) -> Dec (Equal a b)
decEq EQ EQ = Yes Refl
decEq EQ LT = No eqNotLT
decEq EQ GT = No eqNotGT

decEq LT EQ = No (negEqSym eqNotLT)
decEq LT LT = Yes Refl
decEq LT GT = No ltNotGT

decEq GT EQ = No (negEqSym eqNotGT)
decEq GT LT = No (negEqSym ltNotGT)
decEq GT GT = Yes Refl

public export
apply : (op : CompOp)
     -> (a,b : Nat)
            -> Bool
apply EQ = (==)
apply LT = (<)
apply GT = (>)

-- [ EOF ]
