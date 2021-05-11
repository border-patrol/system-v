module SystemV.Common.Types.Nat.Arithmetic

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

public export
data ArithOp = MUL
             | DIV
             | ADD
             | SUB


noMulDiv : Equal MUL DIV -> Void
noMulDiv Refl impossible

noMulAdd : Equal MUL ADD -> Void
noMulAdd Refl impossible

noMulSub : Equal MUL SUB -> Void
noMulSub Refl impossible

noDivAdd : Equal DIV ADD -> Void
noDivAdd Refl impossible

noDivSub : Equal DIV SUB -> Void
noDivSub Refl impossible

noAddSub : Equal ADD SUB -> Void
noAddSub Refl impossible

export
decEq : (a,b : ArithOp) -> Dec (Equal a b)
decEq MUL MUL = Yes Refl
decEq MUL DIV = No noMulDiv
decEq MUL ADD = No noMulAdd
decEq MUL SUB = No noMulSub

decEq DIV MUL = No (negEqSym noMulDiv)
decEq DIV DIV = Yes Refl
decEq DIV ADD = No noDivAdd
decEq DIV SUB = No noDivSub

decEq ADD MUL = No (negEqSym noMulAdd)
decEq ADD DIV = No (negEqSym noDivAdd)
decEq ADD ADD = Yes Refl
decEq ADD SUB = No noAddSub

decEq SUB MUL = No (negEqSym noMulSub)
decEq SUB DIV = No (negEqSym noDivSub)
decEq SUB ADD = No (negEqSym noAddSub)
decEq SUB SUB = Yes Refl

public export
data Valid : ArithOp
          -> Nat
          -> Nat
          -> Type
  where
   MulV  : Valid MUL a b
   DivV  : (prf : IsSucc b)
               -> Valid DIV a b
   AddV : Valid ADD a b
   SubV : Valid SUB a b

public export
data Error = DivByZero

divByZero : (IsSucc b -> Void) -> Valid DIV a b -> Void
divByZero f (DivV prf) = f prf

export
validArithOp : (op : ArithOp)
            -> (a,b : Nat)
                   -> DecInfo Error (Valid op a b)
validArithOp MUL a b = Yes MulV
validArithOp DIV a b with (isItSucc b)
  validArithOp DIV a b | (Yes prf)
    = Yes (DivV prf)
  validArithOp DIV a b | (No contra)
    = No DivByZero (divByZero contra)
validArithOp ADD a b = Yes AddV
validArithOp SUB a b = Yes SubV

public export
apply : (op  : ArithOp)
     -> (a,b : Nat)
     -> (prf : Valid op a b)
            -> Nat
apply op a b prf with (prf)
  apply MUL a b prf | MulV = mult a b
  apply DIV a b prf | (DivV x) with (x)
    apply DIV a (S n) prf | (DivV x) | ItIsSucc = div a (S n)
  apply ADD a b prf | AddV = plus a b
  apply SUB a b prf | SubV = minus a b

-- [ EOF ]
