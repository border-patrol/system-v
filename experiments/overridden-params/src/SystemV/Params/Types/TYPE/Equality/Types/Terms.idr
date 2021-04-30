module SystemV.Params.Types.TYPE.Equality.Types.Terms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Params.Types.TYPE

%default total

export
funcTypeTyNotModuleTy : (Equals Universe TYPE (FuncTy x y) ModuleTy)
                             -> Void
funcTypeTyNotModuleTy (Same Refl Refl) impossible

export
funcTypeTyNotChanTy : (Equals Universe TYPE (FuncTy x y) (ChanTy t))
                           -> Void
funcTypeTyNotChanTy (Same Refl Refl) impossible

export
funcTypeTyNotPortTy : (Equals Universe TYPE (FuncTy x y) (PortTy t d))
                           -> Void
funcTypeTyNotPortTy (Same Refl Refl) impossible

export
funcTypeTyNotNatTy : (Equals Universe TYPE (FuncTy x y) (NatTy n))
                           -> Void
funcTypeTyNotNatTy (Same Refl Refl) impossible

export
funcTypeTyNotUnitTy : (Equals Universe TYPE (FuncTy x y) UnitTy)
                           -> Void
funcTypeTyNotUnitTy (Same Refl Refl) impossible

export
funcTypeTyNotBoolTy : (Equals Universe TYPE (FuncTy x y) BoolTy)
                           -> Void
funcTypeTyNotBoolTy (Same Refl Refl) impossible

export
funcTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                               -> Equals Universe TYPE (FuncTy x a) (FuncTy y b)
                               -> Void
funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                -> Equals Universe TYPE (FuncTy x a) (FuncTy x b)
                                -> Void
funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcTypeNotFuncDefType : (Equals Universe TYPE (FuncTy x y) (FuncDefTy u a b))
                                   -> Void
funcTypeNotFuncDefType (Same Refl Refl) impossible

export
moduleTyNotChanTy : Equals Universe TYPE (ModuleTy) (ChanTy type) -> Void
moduleTyNotChanTy (Same Refl Refl) impossible

export
moduleTyNotPortTy : Equals Universe TYPE (ModuleTy) (PortTy type dir) -> Void
moduleTyNotPortTy (Same Refl Refl) impossible

export
moduleTyNotNatTy : Equals Universe TYPE (ModuleTy) (NatTy n) -> Void
moduleTyNotNatTy (Same Refl Refl) impossible

export
moduleTyNotUnitTy : Equals Universe TYPE (ModuleTy) UnitTy -> Void
moduleTyNotUnitTy (Same Refl Refl) impossible

export
moduleTyNotBoolTy : Equals Universe TYPE (ModuleTy) BoolTy -> Void
moduleTyNotBoolTy (Same Refl Refl) impossible

export
moduleNotFuncDef : Equals Universe TYPE (ModuleTy) (FuncDefTy u a b) -> Void
moduleNotFuncDef (Same Refl Refl) impossible

export
chanTyNotPortTy : Equals Universe TYPE (ChanTy type) (PortTy t d) -> Void
chanTyNotPortTy (Same Refl Refl) impossible

export
chanTyNotNatTy : Equals Universe TYPE (ChanTy type) (NatTy n) -> Void
chanTyNotNatTy (Same Refl Refl) impossible

export
chanTyNotUnitTy : Equals Universe TYPE (ChanTy type) UnitTy -> Void
chanTyNotUnitTy (Same Refl Refl) impossible

export
chanTyNotBoolTy : Equals Universe TYPE (ChanTy type) BoolTy -> Void
chanTyNotBoolTy (Same Refl Refl) impossible

export
chanTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTy x) (ChanTy y))
                             -> Void
chanTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
chanNotFuncDef : Equals Universe TYPE (ChanTy type) (FuncDefTy u t d) -> Void
chanNotFuncDef (Same Refl Refl) impossible

export
portTyNotNatTy : Equals Universe TYPE (PortTy type dir) (NatTy n) -> Void
portTyNotNatTy (Same Refl Refl) impossible

export
portTyNotUnitTy : Equals Universe TYPE (PortTy type dir) UnitTy -> Void
portTyNotUnitTy (Same Refl Refl) impossible

export
portTyNotBoolTy : Equals Universe TYPE (PortTy type dir) BoolTy -> Void
portTyNotBoolTy (Same Refl Refl) impossible

export
portTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTy x a) (PortTy y b))
                             -> Void
portTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
portTyDiffDirs : (contra : a === b -> Void)
                  -> (prf   : Equals Universe TYPE (PortTy type a) (PortTy x b))
                           -> Void
portTyDiffDirs contra (Same Refl Refl) = contra Refl

export
portNotFuncDef : Equals Universe TYPE (PortTy type dir) (FuncDefTy u x y) -> Void
portNotFuncDef (Same Refl Refl) impossible

export
natNotFuncDef : Equals Universe TYPE (NatTy n) (FuncDefTy u x y) -> Void
natNotFuncDef (Same Refl Refl) impossible

export
natTyNotUnitTy : Equals Universe TYPE (NatTy n) UnitTy -> Void
natTyNotUnitTy (Same Refl Refl) impossible

export
natTyNotBoolTy : Equals Universe TYPE (NatTy n) BoolTy -> Void
natTyNotBoolTy (Same Refl Refl) impossible

export
natTyNatsNotSame : (contra : n = m -> Void)
                -> (prf    : Equals Universe TYPE (NatTy n) (NatTy m))
                          -> Void
natTyNatsNotSame contra (Same Refl Refl) = contra Refl

export
unitTyNotFuncDefTy : Equals Universe TYPE UnitTy (FuncDefTy u x y) -> Void
unitTyNotFuncDefTy (Same Refl Refl) impossible

export
unitTyNotBoolTy : Equals Universe TYPE UnitTy BoolTy -> Void
unitTyNotBoolTy (Same Refl Refl) impossible

export
funcDefTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                                  -> Equals Universe TYPE (FuncDefTy u x a) (FuncDefTy u y b)
                                  -> Void
funcDefTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcDefTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                   -> Equals Universe TYPE (FuncDefTy u x a) (FuncDefTy u x b)
                                   -> Void
funcDefTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcDefTypeNotBoolTy : Equals Universe TYPE (FuncDefTy u p r) BoolTy -> Void
funcDefTypeNotBoolTy (Same Refl Refl) impossible


{-
export
decEq : (a,b : TYPE (IDX TERM))
            -> DecInfo Equality.Error
                       (Equals Universe TYPE a b)
decEq a b with (a)
  decEq a b | (FuncTy x y) with (b)
    decEq a b | (FuncTy x y) | (FuncTy z w) with (decEq x z)
      decEq a b | (FuncTy x y) | (FuncTy z w) | (Yes prf) with (prf)
        decEq a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) with (decEq y w)
          decEq a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) | (Yes z) with (z)
            decEq a b | (FuncTy x y) | (FuncTy x y) | (Yes prf) | (Same Refl Refl) | (Yes z) | (Same Refl Refl)
              = Yes (Same Refl Refl)
          decEq a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) | (No msg contra)
            = No msg (funcTypeReturnNotEqual contra)
      decEq a b | (FuncTy x y) | (FuncTy z w) | (No msg contra)
        =  No msg (funcTypeParamNotEqual contra)

    decEq a b | (FuncTy x y) | ModuleTy
      = No (TypeMismatch a b) (funcTypeTyNotModuleTy)
    decEq a b | (FuncTy x y) | (ChanTy type)
      = No (TypeMismatch a b) (funcTypeTyNotChanTy)
    decEq a b | (FuncTy x y) | (PortTy type dir)
      = No (TypeMismatch a b) (funcTypeTyNotPortTy)
    decEq a b | (FuncTy x y) | (NatTy n)
      = No (TypeMismatch a b) (funcTypeTyNotNatTy)
    decEq a b | (FuncTy x y) | UnitTy
      = No (TypeMismatch a b) (funcTypeTyNotUnitTy)
    decEq a b | (FuncTy x y) | (FuncDefTy u f g)
      = No (TypeMismatch a b) (funcTypeNotFuncDefType)
    decEq a b | (FuncTy x y) | BoolTy
      = No (TypeMismatch a b) (funcTypeTyNotBoolTy)


  decEq a b | ModuleTy with (b)
    decEq a b | ModuleTy | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotModuleTy)
    decEq a b | ModuleTy | ModuleTy
      = Yes (Same Refl Refl)
    decEq a b | ModuleTy | (ChanTy type)
      = No (TypeMismatch a b) moduleTyNotChanTy
    decEq a b | ModuleTy | (PortTy type dir)
      = No (TypeMismatch a b) moduleTyNotPortTy
    decEq a b | ModuleTy | (NatTy n)
      = No (TypeMismatch a b) moduleTyNotNatTy
    decEq a b | ModuleTy | UnitTy
      = No (TypeMismatch a b) moduleTyNotUnitTy
    decEq a b | ModuleTy | (FuncDefTy u x y)
      = No (TypeMismatch a b) (moduleNotFuncDef)
    decEq a b | ModuleTy | BoolTy
      = No (TypeMismatch a b) moduleTyNotBoolTy

  decEq a b | (ChanTy type) with (b)
    decEq a b | (ChanTy type) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotChanTy)
    decEq a b | (ChanTy type) | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotChanTy)
    decEq a b | (ChanTy type) | (ChanTy x) with (DataTypes.decEq type x)
      decEq a b | (ChanTy type) | (ChanTy x) | (Yes prf) with (prf)
        decEq a b | (ChanTy type) | (ChanTy type) | (Yes prf) | (Same Refl Refl)
          = Yes (Same Refl Refl)
      decEq a b | (ChanTy type) | (ChanTy x) | (No msg contra)
        = No msg (chanTyDiffTypes contra)
    decEq a b | (ChanTy type) | (PortTy x dir)
      = No (TypeMismatch a b) chanTyNotPortTy
    decEq a b | (ChanTy type) | (NatTy n)
      = No (TypeMismatch a b) chanTyNotNatTy
    decEq a b | (ChanTy type) | UnitTy
      = No (TypeMismatch a b) chanTyNotUnitTy
    decEq a b | (ChanTy type) | (FuncDefTy u x y)
      = No (TypeMismatch a b) chanNotFuncDef
    decEq a b | (ChanTy type) | BoolTy
      = No (TypeMismatch a b) chanTyNotBoolTy

  decEq a b | (PortTy type dir) with (b)
    decEq a b | (PortTy type dir) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotPortTy)
    decEq a b | (PortTy type dir) | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotPortTy)
    decEq a b | (PortTy type dir) | (ChanTy x)
      = No (TypeMismatch a b) (negEqSym chanTyNotPortTy)
    decEq a b | (PortTy type dir) | (PortTy x y) with (DataTypes.decEq type x)
      decEq a b | (PortTy type dir) | (PortTy x y) | (Yes prf) with (prf)
        decEq a b | (PortTy type dir) | (PortTy type y) | (Yes prf) | (Same Refl Refl) with (Direction.decEq dir y)
          decEq a b | (PortTy type y) | (PortTy type y) | (Yes prf) | (Same Refl Refl) | (Yes Refl)
            = Yes (Same Refl Refl)
          decEq a b | (PortTy type dir) | (PortTy type y) | (Yes prf) | (Same Refl Refl) | (No contra)
            = No (TypeMismatch a b) (portTyDiffDirs contra)
      decEq a b | (PortTy type dir) | (PortTy x y) | (No msg contra)
        = No msg (portTyDiffTypes contra)
    decEq a b | (PortTy type dir) | (NatTy n)
      = No (TypeMismatch a b) portTyNotNatTy
    decEq a b | (PortTy type dir) | UnitTy
      = No (TypeMismatch a b) portTyNotUnitTy
    decEq a b | (PortTy type dir) | (FuncDefTy u x y)
      = No (TypeMismatch a b) portNotFuncDef
    decEq a b | (PortTy type dir) | BoolTy
      = No (TypeMismatch a b) portTyNotBoolTy

  decEq a b | (NatTy n) with (b)
    decEq a b | (NatTy n) | (FuncTy param return)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotNatTy)
    decEq a b | (NatTy n) | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotNatTy)
    decEq a b | (NatTy n) | (ChanTy type)
      = No (TypeMismatch a b) (negEqSym chanTyNotNatTy)
    decEq a b | (NatTy n) | (PortTy type dir)
      = No (TypeMismatch a b) (negEqSym portTyNotNatTy)

    decEq a b | (NatTy n) | (NatTy k) with (decEq n k)
      decEq a b | (NatTy k) | (NatTy k) | (Yes Refl)
        = Yes (Same Refl Refl)
      decEq a b | (NatTy n) | (NatTy k) | (No contra)
        = No (TypeMismatch a b) (natTyNatsNotSame contra)

    decEq a b | (NatTy n) | UnitTy
      = No (TypeMismatch a b) natTyNotUnitTy
    decEq a b | (NatTy n) | (FuncDefTy u x y)
      = No (TypeMismatch a b) natNotFuncDef
    decEq a b | (NatTy n) | BoolTy
      = No (TypeMismatch a b) natTyNotBoolTy


  decEq a b | UnitTy with (b)
    decEq a b | UnitTy | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotUnitTy)
    decEq a b | UnitTy | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotUnitTy)
    decEq a b | UnitTy | (ChanTy type)
      = No (TypeMismatch a b) (negEqSym chanTyNotUnitTy)
    decEq a b | UnitTy | (PortTy type dir)
      = No (TypeMismatch a b) (negEqSym portTyNotUnitTy)
    decEq a b | UnitTy | (NatTy n)
      = No (TypeMismatch a b) (negEqSym natTyNotUnitTy)
    decEq a b | UnitTy | UnitTy = Yes (Same Refl Refl)
    decEq a b | UnitTy | (FuncDefTy u x y)
      = No (TypeMismatch a b) unitTyNotFuncDefTy
    decEq a b | UnitTy | (BoolTy)
      = No (TypeMismatch a b) (unitTyNotBoolTy)


  decEq a b | (FuncDefTy u p r ) with (b)
    decEq a b | (FuncDefTy u p r ) | (FuncTy param return)
      = No (TypeMismatch a b) (negEqSym funcTypeNotFuncDefType)
    decEq a b | (FuncDefTy u p r ) | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleNotFuncDef)
    decEq a b | (FuncDefTy u p r ) | (ChanTy type)
      = No (TypeMismatch a b) (negEqSym chanNotFuncDef)
    decEq a b | (FuncDefTy u p r ) | (PortTy type dir)
      = No (TypeMismatch a b) (negEqSym portNotFuncDef)
    decEq a b | (FuncDefTy u p r ) | UnitTy
      = No (TypeMismatch a b) (negEqSym unitTyNotFuncDefTy)
    decEq a b | (FuncDefTy u p r ) | (NatTy k)
      = No (TypeMismatch a b) (negEqSym natNotFuncDef)

    decEq a b | (FuncDefTy u p r) | (FuncDefTy v param return) with (byIndex p param)
      decEq a b | (FuncDefTy v p r) | (FuncDefTy v param return) | (IdxSame p param Refl) with (v)
        decEq a b | (FuncDefTy v p r) | (FuncDefTy v param return) | (IdxSame p param Refl) | (DATA TERM) = ?rhs_rhs_3_rhs_3
        decEq a b | (FuncDefTy v p r) | (FuncDefTy v param return) | (IdxSame p param Refl) | (DATA TYPE) = ?rhs_rhs_3_rhs_4

        decEq a b | (FuncDefTy v p r) | (FuncDefTy v param return) | (IdxSame p param Refl) | (IDX x) = ?rhs_rhs_3_rhs_2
      decEq a b | (FuncDefTy u p r) | (FuncDefTy v param return) | (IdxDiff p param contra)
        = No (TypeMismatch a b) (funcDefParamNotSame contra)

--    with (decEq p param)
--      decEq a b | (FuncDefTy u p r) | (FuncDefTy u param return) | (Yes prf) with (prf)
--        decEq a b | (FuncDefTy u param r) | (FuncDefTy u param return) | (Yes prf) | (Same Refl Refl) with (decEq r return)
--          decEq a b | (FuncDefTy u p r) | (FuncDefTy u param return) | (Yes prf) | (Same Refl Refl) | (Yes z) with (z)
--            decEq a b | (FuncDefTy u p r) | (FuncDefTy u p r) | (Yes prf) | (Same Refl Refl) | (Yes z) | (Same Refl Refl)
--              = Yes (Same Refl Refl)
--          decEq a b | (FuncDefTy u p r) | (FuncDefTy u param return) | (Yes prf) | (Same Refl Refl) | (No msg contra)
--            =  No msg (funcDefTypeReturnNotEqual contra)
--      decEq a b | (FuncDefTy u p r) | (FuncDefTy u param return) | (No msg contra)
--        =  No msg (funcDefTypeParamNotEqual contra)

    decEq a b | (FuncDefTy u p r) | BoolTy
      = No (TypeMismatch a b) funcDefTypeNotBoolTy

  decEq a b | BoolTy with (b)
      decEq a b | BoolTy | (FuncTy param return)
        = No (TypeMismatch a b) (negEqSym funcTypeTyNotBoolTy)
      decEq a b | BoolTy | (FuncDefTy u param return)
        = No (TypeMismatch a b) (negEqSym funcDefTypeNotBoolTy)
      decEq a b | BoolTy | ModuleTy
        = No (TypeMismatch a b) (negEqSym moduleTyNotBoolTy)
      decEq a b | BoolTy | (ChanTy type)
        = No (TypeMismatch a b) (negEqSym chanTyNotBoolTy)
      decEq a b | BoolTy | (PortTy type dir)
        = No (TypeMismatch a b) (negEqSym portTyNotBoolTy)
      decEq a b | BoolTy | UnitTy
        = No (TypeMismatch a b ) (negEqSym unitTyNotBoolTy)
      decEq a b | BoolTy | (NatTy k)
        = No (TypeMismatch a b) (negEqSym natTyNotBoolTy)
      decEq a b | BoolTy | BoolTy
        = Yes (Same Refl Refl)
-}
-- [ EOF ]
