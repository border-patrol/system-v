module SystemV.Params.Types.TYPE.Equality.Types

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality.View
import SystemV.Params.Types.TYPE.Equality.Error

import SystemV.Params.Types.TYPE.Equality.DataTerms
import SystemV.Params.Types.TYPE.Equality.DataTypes

import SystemV.Params.Types.TYPE.Equality.Types.Types
import SystemV.Params.Types.TYPE.Equality.Types.Terms

%default total

idxDiffLevels : (IDX level = IDX level -> Void)
             -> Equals Universe TYPE a b
             -> Void
idxDiffLevels f (Same Refl _) = f Refl

funcDefParamNotSameLevel : (u = v -> Void)
                   -> Equals Universe TYPE (FuncDefTy u p r) (FuncDefTy v param return)
                   -> Void
funcDefParamNotSameLevel f (Same prfIdx Refl) = f Refl

funcDefReturnNotSameType : (Equals Universe TYPE rA rB -> Void)
                        -> Equals Universe TYPE (FuncDefTy v pA rA) (FuncDefTy v pB rB)
                        -> Void
funcDefReturnNotSameType f (Same Refl Refl) = f (Same Refl Refl)

funcDefParamNotSame : (Equals Universe TYPE pA pB -> Void)
                   -> Equals Universe TYPE (FuncDefTy (IDX x) pA rA) (FuncDefTy (IDX x) pB rB)
                   -> Void
funcDefParamNotSame f (Same Refl Refl) = f (Same Refl Refl)

funcDefParamDataNotSame : (Equals Universe TYPE pA pB -> Void)
                       -> Equals Universe TYPE (FuncDefTy (DATA TERM) pA rA) (FuncDefTy (DATA TERM) pB rB)
                       -> Void
funcDefParamDataNotSame f (Same Refl Refl) = f (Same Refl Refl)

funcDefParamDataTypeNotSame : (Equals Universe TYPE pA pB -> Void)
                       -> Equals Universe TYPE (FuncDefTy (DATA TYPE) pA rA) (FuncDefTy (DATA TYPE) pB rB)
                       -> Void
funcDefParamDataTypeNotSame f (Same Refl Refl) = f (Same Refl Refl)

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

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (FuncDefTy u x y)
        = No (TypeMismatch a b) (funcTypeNotFuncDefType)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | ModuleTy
        = No (TypeMismatch a b) (funcTypeTyNotModuleTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (ChanTy type)
        = No (TypeMismatch a b) (funcTypeTyNotChanTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (PortTy type dir)
        = No (TypeMismatch a b) (funcTypeTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | UnitTy
        = No (TypeMismatch a b) (funcTypeTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | (NatTy k)
        = No (TypeMismatch a b) (funcTypeTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncTy param return) | BoolTy
        = No (TypeMismatch a b) (funcTypeTyNotBoolTy)

-- ### Defaulting Functions

    decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (FuncTy x y)
        = No (TypeMismatch a b) (negEqSym funcTypeNotFuncDefType)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (FuncDefTy v pB rB) with (byIndex pA pB)
        decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) with (Types.decEq rA rB)
          decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) with (byIndex pA pB)
            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) with (v)
              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) with (DataTerms.decEq pA pB)
                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) | (Yes prfEq) with (prfWhy)
                  decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rA) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) | (Yes prfEq) | (Same Refl Refl) with (prfEq)
                    decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pB rA) | (FuncDefTy v pB rA) | (IdxSame pB pB Refl) | (Yes prfWhy) | (IdxSame pB pB Refl) | (DATA TERM) | (Yes prfEq) | (Same Refl Refl) | (Same Refl Refl)
                      = Yes (Same Refl Refl)

                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcDefParamDataNotSame prfWhyNot)

              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) with (DataTypes.decEq pA pB)
                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) | (Yes prfEq) with (prfWhy)
                  decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rA) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) | (Yes prfEq) | (Same Refl Refl) with (prfEq)
                    decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pB rA) | (FuncDefTy v pB rA) | (IdxSame pB pB Refl) | (Yes prfWhy) | (IdxSame pB pB Refl) | (DATA TYPE) | (Yes prfEq) | (Same Refl Refl) | (Same Refl Refl)
                      = Yes (Same Refl Refl)

                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcDefParamDataTypeNotSame prfWhyNot)

              decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (IDX x) with (Types.decEq pA pB)
                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfEq) with (prfEq)
                  decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pA rB) | (IdxSame pA pA Refl) | (Yes prfWhy) | (IdxSame pA pA Refl) | (IDX x) | (Yes prfEq) | (Same Refl Refl) with (prfWhy)
                    decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rB) | (FuncDefTy v pA rB) | (IdxSame pA pA Refl) | (Yes prfWhy) | (IdxSame pA pA Refl) | (IDX x) | (Yes prfEq) | (Same Refl Refl) | (Same Refl Refl)
                      = Yes (Same Refl Refl)

                decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (IDX x) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcDefParamNotSame prfWhyNot)

            decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxDiff pA pB contra)
              = No (TypeMismatch a b) (funcDefParamNotSameLevel contra)

          decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (No msgWhyNot prfWhyNot)
            = No (TypeMismatch a b) (funcDefReturnNotSameType prfWhyNot)

        decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (FuncDefTy v pB rB) | (IdxDiff pA pB contra)
          = No (TypeMismatch a b) (funcDefParamNotSameLevel contra)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleNotFuncDef)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (ChanTy type)
        = No (TypeMismatch a b) (negEqSym chanNotFuncDef)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (PortTy type dir)
        = No (TypeMismatch a b) (negEqSym portNotFuncDef)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | UnitTy
        = No (TypeMismatch a b) (negEqSym unitTyNotFuncDefTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (NatTy k)
        = No (TypeMismatch a b) (negEqSym natNotFuncDef)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | BoolTy
        = No (TypeMismatch a b) (funcDefTypeNotBoolTy)

-- ### Modules
    decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotModuleTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (FuncDefTy u param return)
        = No (TypeMismatch a b) (moduleNotFuncDef)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | ModuleTy
        = Yes (Same Refl Refl)

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (ChanTy type)
        = No (TypeMismatch a b) moduleTyNotChanTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (PortTy type dir)
        = No (TypeMismatch a b) moduleTyNotPortTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | UnitTy
        = No (TypeMismatch a b) moduleTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | (NatTy k)
        = No (TypeMismatch a b) moduleTyNotNatTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | ModuleTy | BoolTy
        = No (TypeMismatch a b) moduleTyNotBoolTy

-- ### Channels
    decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotChanTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (FuncDefTy u param return)
        = No (TypeMismatch a b) chanNotFuncDef

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotChanTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (ChanTy type') with (DataTypes.decEq type type')

        decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (ChanTy type') | (Yes prfWhy) with (prfWhy)

          decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (ChanTy type) | (Yes prfWhy) | (Same Refl Refl)
            = Yes (Same Refl Refl)

        decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (ChanTy type') | (No msgWhyNot prfWhyNot)
          = No (TypeMismatch a b) (chanTyDiffTypes prfWhyNot)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (PortTy x dir)
        = No (TypeMismatch a b) chanTyNotPortTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | UnitTy
        = No (TypeMismatch a b) chanTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | (NatTy k)
        = No (TypeMismatch a b) chanTyNotNatTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (ChanTy type) | BoolTy
        = No (TypeMismatch a b) chanTyNotBoolTy

-- ### Ports

    decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (FuncDefTy u param return)
        = No (TypeMismatch a b) portNotFuncDef

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (ChanTy x)
        = No (TypeMismatch a b) (negEqSym chanTyNotPortTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (PortTy type' dir') with (DataTypes.decEq type type')

        decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (PortTy type' dir') | (Yes prfWhy) with (prfWhy)

          decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (PortTy type dir') | (Yes prfWhy) | (Same Refl Refl) with (Direction.decEq dir dir')
            decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir') | (PortTy type dir') | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl)
              =  Yes (Same Refl Refl)

            decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (PortTy type dir') | (Yes prfWhy) | (Same Refl Refl) | (No contra)
              = No (TypeMismatch a b) (portTyDiffDirs contra)

        decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (PortTy type' dir') | (No msgWhyNot prfWhyNot)
          = No (TypeMismatch a b) (portTyDiffTypes prfWhyNot)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | UnitTy
        = No (TypeMismatch a b) portTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | (NatTy k)
        = No (TypeMismatch a b) portTyNotNatTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (PortTy type dir) | BoolTy
        = No (TypeMismatch a b) portTyNotBoolTy

-- ### Unit
    decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (FuncDefTy u param return)
        = No (TypeMismatch a b) unitTyNotFuncDefTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (ChanTy type)
        = No (TypeMismatch a b) (negEqSym chanTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (PortTy type dir)
        = No (TypeMismatch a b) (negEqSym portTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | UnitTy
        = Yes (Same Refl Refl)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | (NatTy k)
        = No (TypeMismatch a b) (negEqSym natTyNotUnitTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | UnitTy | BoolTy
        = No (TypeMismatch a b) unitTyNotBoolTy

-- ### Nats
    decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | (FuncDefTy u param return)
        = No (TypeMismatch a b) natNotFuncDef

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | (ChanTy type)
        = No (TypeMismatch a b) (negEqSym chanTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | (PortTy type dir)
        = No (TypeMismatch a b) (negEqSym portTyNotNatTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | UnitTy
         = No (TypeMismatch a b) natTyNotUnitTy

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | (NatTy j) with (decEq k j)
        decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy j) | (NatTy j) | (Yes Refl)
          = Yes (Same Refl Refl)
        decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | (NatTy j) | (No contra)
          = No (TypeMismatch a b) (natTyNatsNotSame contra)

      decEq a b {level = TERM} | (IdxSame a b Refl) | (NatTy k) | BoolTy
        = No (TypeMismatch a b) natTyNotBoolTy

-- ### Booleans
    decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy with (b)
      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (FuncDefTy u param return)
        = No (TypeMismatch a b) (negEqSym funcDefTypeNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (ChanTy type)
        = No (TypeMismatch a b) (negEqSym chanTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (PortTy type dir)
        = No (TypeMismatch a b) (negEqSym portTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | UnitTy
        = No (TypeMismatch a b ) (negEqSym unitTyNotBoolTy)

      decEq a b {level = TERM} | (IdxSame a b Refl) | BoolTy | (NatTy k)
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

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (FuncDefTy u x y)
        = No (TypeMismatch a b) (funcTypeTyDescNotFuncDefTypeTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | ModuleTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotModuleTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (ChanTyDesc type)
        = No (TypeMismatch a b) (funcTypeTyDescNotChanTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (PortTyDesc type dir)
        = No (TypeMismatch a b) (funcTypeTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | UnitTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | (NatTyDesc k)
        = No (TypeMismatch a b) (funcTypeTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncTy param return) | BoolTyDesc
        = No (TypeMismatch a b) (funcTypeTyDescNotBoolTyDesc)

-- ### Defaulting Functions

    decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (FuncTy x y)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotFuncDefTypeTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (FuncDefTy v pB rB) with (byIndex pA pB)
        decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) with (Types.decEq rA rB)
          decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) with (byIndex pA pB)
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) with (v)
              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) with (DataTerms.decEq pA pB)
                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) | (Yes prfEq) with (prfWhy)
                  decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rA) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) | (Yes prfEq) | (Same Refl Refl) with (prfEq)
                    decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pB rA) | (FuncDefTy v pB rA) | (IdxSame pB pB Refl) | (Yes prfWhy) | (IdxSame pB pB Refl) | (DATA TERM) | (Yes prfEq) | (Same Refl Refl) | (Same Refl Refl)
                      = Yes (Same Refl Refl)

                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TERM) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcDefParamDataNotSame prfWhyNot)

              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) with (DataTypes.decEq pA pB)
                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) | (Yes prfEq) with (prfWhy)
                  decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rA) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) | (Yes prfEq) | (Same Refl Refl) with (prfEq)
                    decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pB rA) | (FuncDefTy v pB rA) | (IdxSame pB pB Refl) | (Yes prfWhy) | (IdxSame pB pB Refl) | (DATA TYPE) | (Yes prfEq) | (Same Refl Refl) | (Same Refl Refl)
                      = Yes (Same Refl Refl)

                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (DATA TYPE) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcDefParamDataTypeNotSame prfWhyNot)

              decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (IDX x) with (Types.decEq pA pB)
                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (IDX x) | (Yes prfEq) with (prfEq)
                  decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pA rB) | (IdxSame pA pA Refl) | (Yes prfWhy) | (IdxSame pA pA Refl) | (IDX x) | (Yes prfEq) | (Same Refl Refl) with (prfWhy)
                    decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rB) | (FuncDefTy v pA rB) | (IdxSame pA pA Refl) | (Yes prfWhy) | (IdxSame pA pA Refl) | (IDX x) | (Yes prfEq) | (Same Refl Refl) | (Same Refl Refl)
                      = Yes (Same Refl Refl)

                decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxSame pA pB Refl) | (IDX x) | (No msgWhyNot prfWhyNot)
                  = No (TypeMismatch a b) (funcDefParamNotSame prfWhyNot)

            decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (Yes prfWhy) | (IdxDiff pA pB contra)
              = No (TypeMismatch a b) (funcDefParamNotSameLevel contra)

          decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy v pA rA) | (FuncDefTy v pB rB) | (IdxSame pA pB Refl) | (No msgWhyNot prfWhyNot)
            = No (TypeMismatch a b) (funcDefReturnNotSameType prfWhyNot)

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (FuncDefTy v pB rB) | (IdxDiff pA pB contra)
          = No (TypeMismatch a b) (funcDefParamNotSameLevel contra)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotFuncDefTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (ChanTyDesc type)
        = No (TypeMismatch a b) (negEqSym chanTyDescNotFuncDefTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (PortTyDesc type dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotFuncDefTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | UnitTyDesc
        = No (TypeMismatch a b) (negEqSym unitTyDescNotFuncDefTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | (NatTyDesc k)
        = No (TypeMismatch a b) (negEqSym natTyDescNotFuncDefTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (FuncDefTy u pA rA) | BoolTyDesc
        = No (TypeMismatch a b) (funcDefTypeNotBoolTyDesc)

-- ### Modules
    decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotModuleTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (FuncDefTy u param return)
        = No (TypeMismatch a b) (moduleTyDescNotFuncDefTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | ModuleTyDesc
        = Yes (Same Refl Refl)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (ChanTyDesc type)
        = No (TypeMismatch a b) moduleTyDescNotChanTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (PortTyDesc type dir)
        = No (TypeMismatch a b) moduleTyDescNotPortTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | UnitTyDesc
        = No (TypeMismatch a b) moduleTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | (NatTyDesc k)
        = No (TypeMismatch a b) moduleTyDescNotNatTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | ModuleTyDesc | BoolTyDesc
        = No (TypeMismatch a b) moduleTyDescNotBoolTyDesc

-- ### Channels
    decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotChanTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (FuncDefTy u param return)
        = No (TypeMismatch a b) chanTyDescNotFuncDefTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotChanTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (ChanTyDesc type') with (DataTypes.decEq type type')

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (ChanTyDesc type') | (Yes prfWhy) with (prfWhy)

          decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (ChanTyDesc type) | (Yes prfWhy) | (Same Refl Refl)
            = Yes (Same Refl Refl)

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (ChanTyDesc type') | (No msgWhyNot prfWhyNot)
          = No (TypeMismatch a b) (chanTyDescDiffTypes prfWhyNot)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (PortTyDesc x dir)
        = No (TypeMismatch a b) chanTyDescNotPortTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | UnitTyDesc
        = No (TypeMismatch a b) chanTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | (NatTyDesc k)
        = No (TypeMismatch a b) chanTyDescNotNatTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (ChanTyDesc type) | BoolTyDesc
        = No (TypeMismatch a b) chanTyDescNotBoolTyDesc

-- ### Ports

    decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (FuncDefTy u param return)
        = No (TypeMismatch a b) portTyDescNotFuncDefTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (ChanTyDesc x)
        = No (TypeMismatch a b) (negEqSym chanTyDescNotPortTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (PortTyDesc type' dir') with (DataTypes.decEq type type')

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (PortTyDesc type' dir') | (Yes prfWhy) with (prfWhy)

          decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (PortTyDesc type dir') | (Yes prfWhy) | (Same Refl Refl) with (Direction.decEq dir dir')
            decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir') | (PortTyDesc type dir') | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl)
              =  Yes (Same Refl Refl)

            decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (PortTyDesc type dir') | (Yes prfWhy) | (Same Refl Refl) | (No contra)
              = No (TypeMismatch a b) (portTyDescDiffDirs contra)

        decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (PortTyDesc type' dir') | (No msgWhyNot prfWhyNot)
          = No (TypeMismatch a b) (portTyDescDiffTypes prfWhyNot)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | UnitTyDesc
        = No (TypeMismatch a b) portTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | (NatTyDesc k)
        = No (TypeMismatch a b) portTyDescNotNatTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (PortTyDesc type dir) | BoolTyDesc
        = No (TypeMismatch a b) portTyDescNotBoolTyDesc

-- ### Unit
    decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (FuncDefTy u param return)
        = No (TypeMismatch a b) unitTyDescNotFuncDefTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (ChanTyDesc type)
        = No (TypeMismatch a b) (negEqSym chanTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (PortTyDesc type dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | UnitTyDesc
        = Yes (Same Refl Refl)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | (NatTyDesc k)
        = No (TypeMismatch a b) (negEqSym natTyDescNotUnitTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | UnitTyDesc | BoolTyDesc
        = No (TypeMismatch a b) unitTyDescNotBoolTyDesc

-- ### Nats
    decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | (FuncDefTy u param return)
        = No (TypeMismatch a b) natTyDescNotFuncDefTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | (ChanTyDesc type)
        = No (TypeMismatch a b) (negEqSym chanTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | (PortTyDesc type dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotNatTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | UnitTyDesc
         = No (TypeMismatch a b) natTyDescNotUnitTyDesc

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | (NatTyDesc j) with (decEq k j)
        decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc j) | (NatTyDesc j) | (Yes Refl)
          = Yes (Same Refl Refl)
        decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | (NatTyDesc j) | (No contra)
          = No (TypeMismatch a b) (natTyNatsNotSame contra)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | (NatTyDesc k) | BoolTyDesc
        = No (TypeMismatch a b) natTyDescNotBoolTyDesc

-- ### Booleans
    decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc with (b)
      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (FuncDefTy u param return)
        = No (TypeMismatch a b) (negEqSym funcDefTypeNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | ModuleTyDesc
        = No (TypeMismatch a b) (negEqSym moduleTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (ChanTyDesc type)
        = No (TypeMismatch a b) (negEqSym chanTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (PortTyDesc type dir)
        = No (TypeMismatch a b) (negEqSym portTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | UnitTyDesc
        = No (TypeMismatch a b ) (negEqSym unitTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | (NatTyDesc k)
        = No (TypeMismatch a b) (negEqSym natTyDescNotBoolTyDesc)

      decEq a b {level = TYPE} | (IdxSame a b Refl) | BoolTyDesc | BoolTyDesc
        = Yes (Same Refl Refl)

  decEq a b {level = level} | (IdxDiff a b contra)
    = No (TypeMismatch a b) (idxDiffLevels contra)

-- [ EOF ]
