||| A set of structures to describe primitive gates.
module SystemV.Common.Types.Gate

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

%default total

public export
data GateKind = AND  | XOR  | IOR
              | NAND | XNOR | NIOR

andXor   : AND = XOR  -> Void
andXor Refl impossible

andIor   : AND = IOR  -> Void
andIor Refl impossible

andNand  : AND = NAND -> Void
andNand Refl impossible

andXnor  : AND = XNOR -> Void
andXnor Refl impossible

andNior  : AND = NIOR -> Void
andNior Refl impossible

xorIor   : XOR = IOR  -> Void
xorIor Refl impossible

xorNand  : XOR = NAND -> Void
xorNand Refl impossible

xorXnor  : XOR = XNOR -> Void
xorXnor Refl impossible

xorNior  : XOR = NIOR -> Void
xorNior Refl impossible

iorNand  : IOR = NAND -> Void
iorNand Refl impossible

iorXnor  : IOR = XNOR -> Void
iorXnor Refl impossible

iorNior  : IOR = NIOR -> Void
iorNior Refl impossible

nandXnor  : NAND = XNOR -> Void
nandXnor Refl impossible

nandNior  : NAND = NIOR -> Void
nandNior Refl impossible

xnorNior  : XNOR = NIOR -> Void
xnorNior Refl impossible

||| Standard definition of decidable equality.
export
DecEq GateKind where
  decEq AND AND  = Yes Refl
  decEq AND XOR  = No andXor
  decEq AND IOR  = No andIor
  decEq AND NAND = No andNand
  decEq AND XNOR = No andXnor
  decEq AND NIOR = No andNior

  decEq XOR AND  = No (negEqSym andXor)
  decEq XOR XOR  = Yes Refl
  decEq XOR IOR  = No xorIor
  decEq XOR NAND = No xorNand
  decEq XOR XNOR = No xorXnor
  decEq XOR NIOR = No xorNior

  decEq IOR AND  = No (negEqSym andIor)
  decEq IOR XOR  = No (negEqSym xorIor)
  decEq IOR IOR  = Yes Refl
  decEq IOR NAND = No iorNand
  decEq IOR XNOR = No iorXnor
  decEq IOR NIOR = No iorNior

  decEq NAND AND  = No (negEqSym andNand)
  decEq NAND XOR  = No (negEqSym xorNand)
  decEq NAND IOR  = No (negEqSym iorNand)
  decEq NAND NAND = Yes Refl
  decEq NAND XNOR = No nandXnor
  decEq NAND NIOR = No nandNior

  decEq XNOR AND  = No (negEqSym andXnor)
  decEq XNOR XOR  = No (negEqSym xorXnor)
  decEq XNOR IOR  = No (negEqSym iorXnor)
  decEq XNOR NAND = No (negEqSym nandXnor)
  decEq XNOR XNOR = Yes Refl
  decEq XNOR NIOR = No xnorNior

  decEq NIOR AND  = No (negEqSym andNior)
  decEq NIOR XOR  = No (negEqSym xorNior)
  decEq NIOR IOR  = No (negEqSym iorNior)
  decEq NIOR NAND = No (negEqSym nandNior)
  decEq NIOR XNOR = No (negEqSym xnorNior)
  decEq NIOR NIOR = Yes Refl


-- [ EOF ]
