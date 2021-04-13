module SystemV.Types.TYPE.Equality.TypeTerms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Types.TYPE

import SystemV.Types.TYPE.Equality.Error
import SystemV.Types.TYPE.Equality.DataTypes

%default total


funcTypeTyNotModuleTy : (Equals Universe TYPE (FuncTy x y) ModuleTy)
                             -> Void
funcTypeTyNotModuleTy (Same Refl Refl) impossible

funcTypeTyNotChanTy : (Equals Universe TYPE (FuncTy x y) (ChanTy t))
                           -> Void
funcTypeTyNotChanTy (Same Refl Refl) impossible

funcTypeTyNotPortTy : (Equals Universe TYPE (FuncTy x y) (PortTy t d))
                           -> Void
funcTypeTyNotPortTy (Same Refl Refl) impossible

funcTypeTyNotNatTy : (Equals Universe TYPE (FuncTy x y) (NatTy n))
                           -> Void
funcTypeTyNotNatTy (Same Refl Refl) impossible

funcTypeTyNotUnitTy : (Equals Universe TYPE (FuncTy x y) UnitTy)
                           -> Void
funcTypeTyNotUnitTy (Same Refl Refl) impossible

funcTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                               -> Equals Universe TYPE (FuncTy x a) (FuncTy y b)
                               -> Void
funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

funcTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                -> Equals Universe TYPE (FuncTy x a) (FuncTy x b)
                                -> Void
funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

moduleTyNotChanTy : Equals Universe TYPE (ModuleTy) (ChanTy type) -> Void
moduleTyNotChanTy (Same Refl Refl) impossible

moduleTyNotPortTy : Equals Universe TYPE (ModuleTy) (PortTy type dir) -> Void
moduleTyNotPortTy (Same Refl Refl) impossible

moduleTyNotNatTy : Equals Universe TYPE (ModuleTy) (NatTy n) -> Void
moduleTyNotNatTy (Same Refl Refl) impossible

moduleTyNotUnitTy : Equals Universe TYPE (ModuleTy) UnitTy -> Void
moduleTyNotUnitTy (Same Refl Refl) impossible

chanTyNotPortTy : Equals Universe TYPE (ChanTy type) (PortTy t d) -> Void
chanTyNotPortTy (Same Refl Refl) impossible

chanTyNotNatTy : Equals Universe TYPE (ChanTy type) (NatTy n) -> Void
chanTyNotNatTy (Same Refl Refl) impossible

chanTyNotUnitTy : Equals Universe TYPE (ChanTy type) UnitTy -> Void
chanTyNotUnitTy (Same Refl Refl) impossible

chanTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTy x) (ChanTy y))
                             -> Void
chanTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

portTyNotNatTy : Equals Universe TYPE (PortTy type dir) (NatTy n) -> Void
portTyNotNatTy (Same Refl Refl) impossible

portTyNotUnitTy : Equals Universe TYPE (PortTy type dir) UnitTy -> Void
portTyNotUnitTy (Same Refl Refl) impossible

portTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTy x a) (PortTy y b))
                             -> Void
portTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

portTyDiffDirs : (contra : a === b -> Void)
                  -> (prf   : Equals Universe TYPE (PortTy type a) (PortTy x b))
                           -> Void
portTyDiffDirs contra (Same Refl Refl) = contra Refl


natTyNotUnitTy : Equals Universe TYPE (NatTy n) UnitTy -> Void
natTyNotUnitTy (Same Refl Refl) impossible

natTyNatsNotSame : (contra : n = m -> Void)
                -> (prf    : Equals Universe TYPE (NatTy n) (NatTy m))
                          -> Void
natTyNatsNotSame contra (Same Refl Refl) = contra Refl


export
decEq : (a,b : TYPE (IDX TERM))
                      -> DecInfo Equality.Error (Equals Universe TYPE a b)
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


-- [ EOF ]
