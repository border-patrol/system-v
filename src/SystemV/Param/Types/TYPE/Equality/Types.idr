module SystemV.Param.Types.TYPE.Equality.Types

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE
import SystemV.Param.Types.TYPE.Equality.View
import SystemV.Param.Types.TYPE.Equality.Error

import SystemV.Param.Types.TYPE.Equality.DataTerms
import SystemV.Param.Types.TYPE.Equality.DataTypes
import  SystemV.Param.Types.TYPE.Equality.Data

import SystemV.Param.Types.TYPE.Equality.Types.Types
import SystemV.Param.Types.TYPE.Equality.Types.Terms

%default total

idxDiffLevels : (IDX level = IDX level -> Void)
             -> Equals Universe TYPE a b
             -> Void
idxDiffLevels f (Same Refl _) = f Refl

funcParamTyReturnNotSameType : (Equals Universe TYPE rA rB -> Void)
                        -> Equals Universe TYPE (FuncParamTy u pA rA) (FuncParamTy u pB rB)
                        -> Void
funcParamTyReturnNotSameType f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyNotSame : (Equals Universe TYPE pA pB -> Void)
                   -> Equals Universe TYPE (FuncParamTy u pA rA) (FuncParamTy u pB rB)
                   -> Void
funcParamTyNotSame f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyDataTermParamDiff : (Equals Universe TYPE pA pB -> Void) -> Equals Universe TYPE (FuncParamTy (DATA x) pA rA) (FuncParamTy (DATA x) pB rB) -> Void
funcParamTyDataTermParamDiff f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyTermDataReturnDiff : (Equals Universe TYPE rA rB -> Void) -> Equals Universe TYPE (FuncParamTy (DATA x) pA rA) (FuncParamTy (DATA x) pA rB) -> Void
funcParamTyTermDataReturnDiff f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyTermIdxDiff : (u = y -> Void) -> Equals Universe TYPE (FuncParamTy u pA rA) (FuncParamTy y pB rB) -> Void
funcParamTyTermIdxDiff f (Same Refl Refl) = f Refl

funcParamTyTermIdxTermParamDiff : (Equals Universe TYPE pA pB -> Void) -> Equals Universe TYPE (FuncParamTy (IDX x) pA rA) (FuncParamTy (IDX x) pB rB) -> Void
funcParamTyTermIdxTermParamDiff f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyTermIdxTermReturnDiff : (Equals Universe TYPE rA rB -> Void) -> Equals Universe TYPE (FuncParamTy (IDX x) pA rA) (FuncParamTy (IDX x) pB rB) -> Void
funcParamTyTermIdxTermReturnDiff f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyTermIdxDataParamDiff : (Equals Universe TYPE pA pB -> Void) -> Equals Universe TYPE (FuncParamTy (DATA x) pA rA) (FuncParamTy (DATA x) pB rB) -> Void
funcParamTyTermIdxDataParamDiff f (Same Refl Refl) = f (Same Refl Refl)

funcParamTyTermIdxDataReturnDiff : (Equals Universe TYPE rA rB -> Void) -> Equals Universe TYPE (FuncParamTy (DATA x) pA rA) (FuncParamTy (DATA x) pA rB) -> Void
funcParamTyTermIdxDataReturnDiff f (Same Refl Refl) = f (Same Refl Refl)

export
decEq : {level : Level}
     -> (a,b   : TYPE (IDX level))
              -> DecInfo Equality.Error
                        (Equals Universe TYPE a b)
decEq a b {level} with (byIndex a b)
-- ## Terms
  decEq a b {level = TERM} | (IdxSame a b Refl) with (a)
-- ### Functions
    decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) with (b)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param' return') with (decEq param param')

        decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param' return') | (Yes prfWhy) with (prfWhy)

          decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return') | (Yes prfWhy) | (Same Refl Refl) with (decEq return return')
            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return') | (Yes prfWhy) | (Same Refl Refl) | (Yes prfRet) with (prfRet)
              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return) | (Yes prfWhy) | (Same Refl Refl) | (Yes prfRet) | (Same Refl Refl)
                = Yes (Same Refl Refl)

            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return') | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
              = No (TypeMismatch a b) (Terms.funcTypeReturnNotEqual prfWhyNot)

        decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param' return') | (No msgWhyNot prfWhyNot)
          = No (TypeMismatch a b) (Terms.funcTypeParamNotEqual prfWhyNot)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncParamTy u x y)
        = No (TypeMismatch a b) (funcTypeNotFuncParamType)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | ModuleTy
        = No (TypeMismatch a b) (funcTypeTyNotModuleTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | ChanTy
        = No (TypeMismatch a b) (funcTypeTyNotChanTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (PortTy dir)
        = No (TypeMismatch a b) (funcTypeTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | UnitTy
        = No (TypeMismatch a b) (funcTypeTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | NatTy
        = No (TypeMismatch a b) (funcTypeTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | BoolTy
        = No (TypeMismatch a b) (funcTypeTyNotBoolTy)

-- ### Paramaulting Functions

    decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (FuncTy x y)
        = No (TypeMismatch a b) (negEqSym funcTypeNotFuncParamType)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (FuncParamTy y pB rB) with (byIndex pA pB)
        decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) with (y)

          decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (DATA x) with (Data.decEq pA pB)
            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (DATA x) | (Yes prfA) with (prfA)
              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rB) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) with (decEq rA rB)
                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rB) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) | (Yes prfR) with (prfR)
                  decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rA) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) | (Yes prfR) | (Same Refl Refl)
                    = Yes (Same Refl Refl)
                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rB) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcParamTyTermDataReturnDiff prfWhyNot)
            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (DATA x) | (No msgWhyNot prfWhyNot)
              = No (TypeMismatch a b) (funcParamTyDataTermParamDiff prfWhyNot)

          decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) with (decEq pA pB)
            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfA) with (decEq rA rB)
              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfA) | (Yes prfR) with (prfA)
                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pB rA) | (FuncParamTy y pB rB) | (IdxSame pB pB Refl) | (IDX x) | (Yes prfA) | (Yes prfR) | (Same Refl Refl) with (prfR)
                  decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pB rA) | (FuncParamTy y pB rA) | (IdxSame pB pB Refl) | (IDX x) | (Yes prfA) | (Yes prfR) | (Same Refl Refl) | (Same Refl Refl)
                    = Yes (Same Refl Refl)
              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfA) | (No msgWhyNot prfWhyNot)
                = No (TypeMismatch a b) (funcParamTyTermIdxTermReturnDiff prfWhyNot)

            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (No msgWhyNot prfWhyNot)
              = No (TypeMismatch a b) (funcParamTyTermIdxTermParamDiff prfWhyNot)

        decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (FuncParamTy y pB rB) | (IdxDiff pA pB prf)
          = No (TypeMismatch a b) (funcParamTyTermIdxDiff prf)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleNotFuncParam)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | ChanTy
        = No (TypeMismatch a b) (negEqSym chanNotFuncParam)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (PortTy dir)
        = No (TypeMismatch a b) (negEqSym portNotFuncParam)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | UnitTy
        = No (TypeMismatch a b) (negEqSym unitTyNotFuncParamTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | NatTy
        = No (TypeMismatch a b) (negEqSym natNotFuncParam)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | BoolTy
        = No (TypeMismatch a b) (funcParamTypeNotBoolTy)

-- ### Modules
    decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotModuleTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (FuncParamTy u param return)
        = No (TypeMismatch a b) (moduleNotFuncParam)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | ModuleTy
        = Yes (Same Refl Refl)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | ChanTy
        = No (TypeMismatch a b) moduleTyNotChanTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (PortTy dir)
        = No (TypeMismatch a b) moduleTyNotPortTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | UnitTy
        = No (TypeMismatch a b) moduleTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | NatTy
        = No (TypeMismatch a b) moduleTyNotNatTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | BoolTy
        = No (TypeMismatch a b) moduleTyNotBoolTy

-- ### Channels
    decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotChanTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | (FuncParamTy u param return)
        = No (TypeMismatch a b) chanNotFuncParam

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotChanTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | ChanTy
        = Yes (Same Refl Refl)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | (PortTy dir)
        = No (TypeMismatch a b) chanTyNotPortTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | UnitTy
        = No (TypeMismatch a b) chanTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | NatTy
        = No (TypeMismatch a b) chanTyNotNatTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ChanTy | BoolTy
        = No (TypeMismatch a b) chanTyNotBoolTy

-- ### Ports

    decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | (FuncParamTy u param return)
        = No (TypeMismatch a b) portNotFuncParam

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | ChanTy
        = No (TypeMismatch a b) (negEqSym chanTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | (PortTy  dir') with (Direction.decEq dir dir')
            decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir') | (PortTy dir') | (Yes Refl)
              =  Yes (Same Refl Refl)

            decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | (PortTy dir') | (No contra)
              = No (TypeMismatch a b) (portTyDiffDirs contra)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | UnitTy
        = No (TypeMismatch a b) portTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | NatTy
        = No (TypeMismatch a b) portTyNotNatTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy dir) | BoolTy
        = No (TypeMismatch a b) portTyNotBoolTy

-- ### Unit
    decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (FuncParamTy u param return)
        = No (TypeMismatch a b) unitTyNotFuncParamTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | ChanTy
        = No (TypeMismatch a b) (negEqSym chanTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (PortTy dir)
        = No (TypeMismatch a b) (negEqSym portTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | UnitTy
        = Yes (Same Refl Refl)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | NatTy
        = No (TypeMismatch a b) (negEqSym natTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | BoolTy
        = No (TypeMismatch a b) unitTyNotBoolTy

-- ### Nats
    decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | (FuncParamTy u param return)
        = No (TypeMismatch a b) natNotFuncParam

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | ChanTy
        = No (TypeMismatch a b) (negEqSym chanTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | (PortTy dir)
        = No (TypeMismatch a b) (negEqSym portTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | UnitTy
         = No (TypeMismatch a b) natTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | NatTy
        = Yes (Same Refl Refl)

      decEq a b {level = TERM} | (IdxSame a b Refl) | NatTy | BoolTy
        = No (TypeMismatch a b) natTyNotBoolTy

-- ### Booleans
    decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (FuncParamTy u param return)
        = No (TypeMismatch a b) (negEqSym funcParamTypeNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | ChanTy
        = No (TypeMismatch a b) (negEqSym chanTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (PortTy dir)
        = No (TypeMismatch a b) (negEqSym portTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | UnitTy
        = No (TypeMismatch a b ) (negEqSym unitTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | NatTy
        = No (TypeMismatch a b) (negEqSym natTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | BoolTy
        = Yes (Same Refl Refl)



-- ## Types
  decEq a b {level = TYPE} | (IdxSame a b Refl) with (a)
-- ### Functions
    decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) with (b)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param' return') with (decEq param param')

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param' return') | (Yes prfWhy) with (prfWhy)

          decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return') | (Yes prfWhy) | (Same Refl Refl) with (decEq return return')
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return') | (Yes prfWhy) | (Same Refl Refl) | (Yes prfRet) with (prfRet)
              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return) | (Yes prfWhy) | (Same Refl Refl) | (Yes prfRet) | (Same Refl Refl)
                = Yes (Same Refl Refl)

            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param return') | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
              = No (TypeMismatch a b) (Types.funcTypeReturnNotEqual prfWhyNot)

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncTy param' return') | (No msgWhyNot prfWhyNot)
          = No (TypeMismatch a b) (Types.funcTypeParamNotEqual prfWhyNot)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncParamTy u x y)
        = No (TypeMismatch a b) (funcTypeTyDescNotFuncParamTypeTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | ModuleTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotModuleTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | ChanTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotChanTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (PortTyDesc dir)
        = No (TypeMismatch a b) (funcTypeTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | UnitTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | NatTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | BoolTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotBoolTyDesc)

-- ### Paramaulting Functions

    decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (FuncTy x y)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotFuncParamTypeTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (FuncParamTy y pB rB) with (byIndex pA pB)
        decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) with (y)

          decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (DATA x) with (Data.decEq pA pB)
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (DATA x) | (Yes prfA) with (prfA)
              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rB) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) with (decEq rA rB)
                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rB) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) | (Yes prfR) with (prfR)
                  decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rA) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) | (Yes prfR) | (Same Refl Refl)
                    = Yes (Same Refl Refl)
                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pA rB) | (IdxSame pA pA Refl) | (DATA x) | (Yes prfA) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcParamTyTermIdxDataReturnDiff prfWhyNot)
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (DATA x) | (No msgWhyNot prfWhyNot)
              = No (TypeMismatch a b) (funcParamTyTermIdxDataParamDiff prfWhyNot)

          decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) with (decEq pA pB)
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfA) with (decEq rA rB)
              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfA) | (Yes prfR) with (prfA)
                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pB rA) | (FuncParamTy y pB rB) | (IdxSame pB pB Refl) | (IDX x) | (Yes prfA) | (Yes prfR) | (Same Refl Refl) with (prfR)
                  decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pB rA) | (FuncParamTy y pB rA) | (IdxSame pB pB Refl) | (IDX x) | (Yes prfA) | (Yes prfR) | (Same Refl Refl) | (Same Refl Refl)
                    = Yes (Same Refl Refl)
              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfA) | (No msgWhyNot prfWhyNot)
                = No (TypeMismatch a b) (funcParamTyTermIdxTermReturnDiff prfWhyNot)

            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy y pA rA) | (FuncParamTy y pB rB) | (IdxSame pA pB Refl) | (IDX x) | (No msgWhyNot prfWhyNot)
              = No (TypeMismatch a b) (funcParamTyTermIdxTermParamDiff prfWhyNot)

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (FuncParamTy y pB rB) | (IdxDiff pA pB prf)
          = No (TypeMismatch a b) (funcParamTyTermIdxDiff prf)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotFuncParamTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | ChanTyDesc
        = No (TypeMismatch a b) (negEqSym chanTyDescNotFuncParamTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | (PortTyDesc dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotFuncParamTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | UnitTyDesc
        = No (TypeMismatch a b) (negEqSym unitTyDescNotFuncParamTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | NatTyDesc
        = No (TypeMismatch a b) (negEqSym natTyDescNotFuncParamTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncParamTy u pA rA) | BoolTyDesc
        = No (TypeMismatch a b) (funcParamTyNotBoolTyDesc)

-- ### Modules
    decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotModuleTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (FuncParamTy u param return)
        = No (TypeMismatch a b) (moduleTyDescNotFuncParamTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | ModuleTyDesc
        = Yes (Same Refl Refl)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | ChanTyDesc
        = No (TypeMismatch a b) moduleTyDescNotChanTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (PortTyDesc dir)
        = No (TypeMismatch a b) moduleTyDescNotPortTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | UnitTyDesc
        = No (TypeMismatch a b) moduleTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | NatTyDesc
        = No (TypeMismatch a b) moduleTyDescNotNatTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | BoolTyDesc
        = No (TypeMismatch a b) moduleTyDescNotBoolTyDesc

-- ### Channels
    decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotChanTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | (FuncParamTy u param return)
        = No (TypeMismatch a b) chanTyDescNotFuncParamTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotChanTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | ChanTyDesc
        = Yes (Same Refl Refl)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | (PortTyDesc dir)
        = No (TypeMismatch a b) chanTyDescNotPortTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | UnitTyDesc
        = No (TypeMismatch a b) chanTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | NatTyDesc
        = No (TypeMismatch a b) chanTyDescNotNatTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ChanTyDesc | BoolTyDesc
        = No (TypeMismatch a b) chanTyDescNotBoolTyDesc

-- ### Ports

    decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | (FuncParamTy u param return)
        = No (TypeMismatch a b) portTyDescNotFuncParamTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | ChanTyDesc
        = No (TypeMismatch a b) (negEqSym chanTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | (PortTyDesc  dir') with (Direction.decEq dir dir')
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir') | (PortTyDesc dir') | (Yes Refl)
              =  Yes (Same Refl Refl)

            decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | (PortTyDesc dir') | (No contra)
              = No (TypeMismatch a b) (portTyDescDiffDirs contra)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | UnitTyDesc
        = No (TypeMismatch a b) portTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | NatTyDesc
        = No (TypeMismatch a b) portTyDescNotNatTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc dir) | BoolTyDesc
        = No (TypeMismatch a b) portTyDescNotBoolTyDesc

-- ### Unit
    decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (FuncParamTy u param return)
        = No (TypeMismatch a b) unitTyDescNotFuncParamTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | ChanTyDesc
        = No (TypeMismatch a b) (negEqSym chanTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (PortTyDesc dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | UnitTyDesc
        = Yes (Same Refl Refl)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | NatTyDesc
        = No (TypeMismatch a b) (negEqSym natTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | BoolTyDesc
        = No (TypeMismatch a b) unitTyDescNotBoolTyDesc

-- ### Nats
    decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | (FuncParamTy u param return)
        = No (TypeMismatch a b) natTyDescNotFuncParamTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | ChanTyDesc
        = No (TypeMismatch a b) (negEqSym chanTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | (PortTyDesc dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | UnitTyDesc
         = No (TypeMismatch a b) natTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | NatTyDesc
         = Yes (Same Refl Refl)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | NatTyDesc | BoolTyDesc
         = No (TypeMismatch a b) natTyDescNotBoolTyDesc

-- ### Booleans
    decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (FuncParamTy u param return)
        = No (TypeMismatch a b) (negEqSym funcParamTyNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | ChanTyDesc
        = No (TypeMismatch a b) (negEqSym chanTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (PortTyDesc dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | UnitTyDesc
        = No (TypeMismatch a b ) (negEqSym unitTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | NatTyDesc
        = No (TypeMismatch a b) (negEqSym natTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | BoolTyDesc
        = Yes (Same Refl Refl)

  decEq a b {level = level} | (IdxDiff a b contra)
    = No (TypeMismatch a b) (idxDiffLevels contra)

-- [ EOF ]
