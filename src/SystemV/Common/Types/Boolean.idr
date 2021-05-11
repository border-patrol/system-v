module SystemV.Common.Types.Boolean

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

public export
data BoolBinOp = AND
               | IOR
               | XOR

andNotIOR : AND = IOR -> Void
andNotIOR Refl impossible

andNotXOR : AND = XOR -> Void
andNotXOR Refl impossible

ltNotXOR : IOR = XOR -> Void
ltNotXOR Refl impossible

export
decEq : (a,b : BoolBinOp) -> Dec (Equal a b)
decEq AND AND = Yes Refl
decEq AND IOR = No andNotIOR
decEq AND XOR = No andNotXOR

decEq IOR AND = No (negEqSym andNotIOR)
decEq IOR IOR = Yes Refl
decEq IOR XOR = No ltNotXOR

decEq XOR AND = No (negEqSym andNotXOR)
decEq XOR IOR = No (negEqSym ltNotXOR)
decEq XOR XOR = Yes Refl

public export
apply : (op  : BoolBinOp)
     -> (a,b : Bool)
            -> Bool
apply AND a b = a && b
apply IOR a b = a || b
apply XOR a b = (not (a && b)) && (a || b)

-- [ EOF ]
