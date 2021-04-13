module SystemV.Types.TYPE.Equality.TypeTypes

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Types.TYPE

import SystemV.Types.TYPE.Equality.Error
import SystemV.Types.TYPE.Equality.DataTypes

%default total


funcTypeTyDescNotModuleTyDesc : (Equals Universe TYPE (FuncTy x y) ModuleTyDesc)
                             -> Void
funcTypeTyDescNotModuleTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotChanTyDesc : (Equals Universe TYPE (FuncTy x y) (ChanTyDesc t))
                           -> Void
funcTypeTyDescNotChanTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotPortTyDesc : (Equals Universe TYPE (FuncTy x y) (PortTyDesc t d))
                           -> Void
funcTypeTyDescNotPortTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotUnitTyDesc : (Equals Universe TYPE (FuncTy x y) UnitTyDesc)
                           -> Void
funcTypeTyDescNotUnitTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotNatTyDesc : (Equals Universe TYPE (FuncTy x y) (NatTyDesc n))
                           -> Void
funcTypeTyDescNotNatTyDesc (Same Refl Refl) impossible


funcTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                               -> Equals Universe TYPE (FuncTy x a) (FuncTy y b)
                               -> Void
funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

funcTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                -> Equals Universe TYPE (FuncTy x a) (FuncTy x b)
                                -> Void
funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

moduleTyDescNotChanTyDesc : Equals Universe TYPE (ModuleTyDesc) (ChanTyDesc type) -> Void
moduleTyDescNotChanTyDesc (Same Refl Refl) impossible

moduleTyDescNotPortTyDesc : Equals Universe TYPE (ModuleTyDesc) (PortTyDesc type dir) -> Void
moduleTyDescNotPortTyDesc (Same Refl Refl) impossible

moduleTyDescNotUnitTyDesc : Equals Universe TYPE (ModuleTyDesc) UnitTyDesc -> Void
moduleTyDescNotUnitTyDesc (Same Refl Refl) impossible

moduleTyDescNotNatTyDesc : Equals Universe TYPE (ModuleTyDesc) (NatTyDesc n) -> Void
moduleTyDescNotNatTyDesc (Same Refl Refl) impossible


chanTyDescNotPortTyDesc : Equals Universe TYPE (ChanTyDesc type) (PortTyDesc t d) -> Void
chanTyDescNotPortTyDesc (Same Refl Refl) impossible

chanTyDescNotUnitTyDesc : Equals Universe TYPE (ChanTyDesc type) UnitTyDesc -> Void
chanTyDescNotUnitTyDesc (Same Refl Refl) impossible

chanTyDescNotNatTyDesc : Equals Universe TYPE (ChanTyDesc type) (NatTyDesc n) -> Void
chanTyDescNotNatTyDesc (Same Refl Refl) impossible

chanTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTyDesc x) (ChanTyDesc y))
                             -> Void
chanTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

portTyDescNotUnitTyDesc : Equals Universe TYPE (PortTyDesc type dir) UnitTyDesc -> Void
portTyDescNotUnitTyDesc (Same Refl Refl) impossible

portTyDescNotNatTyDesc : Equals Universe TYPE (PortTyDesc type dir) (NatTyDesc n) -> Void
portTyDescNotNatTyDesc (Same Refl Refl) impossible


portTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTyDesc x a) (PortTyDesc y b))
                             -> Void
portTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

portTyDescDiffDirs : (contra : a === b -> Void)
                  -> (prf    : Equals Universe TYPE (PortTyDesc x a) (PortTyDesc x b))
                            -> Void
portTyDescDiffDirs contra (Same Refl Refl) = contra Refl

natTyDescNotUnitTyDesc : Equals Universe TYPE (NatTyDesc n) UnitTyDesc -> Void
natTyDescNotUnitTyDesc (Same Refl Refl) impossible

natTyNatsNotSame : (contra : n = m -> Void)
                -> (prf    : Equals Universe TYPE (NatTyDesc n) (NatTyDesc m))
                          -> Void
natTyNatsNotSame contra (Same Refl Refl) = contra Refl

export
decEq : (a,b : TYPE (IDX TYPE))
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
            =  No msg (funcTypeReturnNotEqual contra)
      decEq a b | (FuncTy x y) | (FuncTy z w) | (No msg contra)
        =  No msg (funcTypeParamNotEqual contra)

    decEq a b | (FuncTy x y) | ModuleTyDesc
      = No (TypeMismatch a b) (funcTypeTyDescNotModuleTyDesc)
    decEq a b | (FuncTy x y) | (ChanTyDesc type)
      = No (TypeMismatch a b) (funcTypeTyDescNotChanTyDesc)
    decEq a b | (FuncTy x y) | (PortTyDesc type dir)
      = No (TypeMismatch a b) (funcTypeTyDescNotPortTyDesc)
    decEq a b | (FuncTy x y) | (NatTyDesc n)
      = No (TypeMismatch a b) (funcTypeTyDescNotNatTyDesc)
    decEq a b | (FuncTy x y) | UnitTyDesc
      = No (TypeMismatch a b) (funcTypeTyDescNotUnitTyDesc)

  decEq a b | ModuleTyDesc with (b)
    decEq a b | ModuleTyDesc | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotModuleTyDesc)
    decEq a b | ModuleTyDesc | ModuleTyDesc
      = Yes (Same Refl Refl)
    decEq a b | ModuleTyDesc | (ChanTyDesc type)
      = No (TypeMismatch a b) moduleTyDescNotChanTyDesc
    decEq a b | ModuleTyDesc | (PortTyDesc type dir)
      = No (TypeMismatch a b) moduleTyDescNotPortTyDesc
    decEq a b | ModuleTyDesc | (NatTyDesc n)
      = No (TypeMismatch a b) moduleTyDescNotNatTyDesc
    decEq a b | ModuleTyDesc | UnitTyDesc
      = No (TypeMismatch a b) moduleTyDescNotUnitTyDesc

  decEq a b | (ChanTyDesc type) with (b)
    decEq a b | (ChanTyDesc type) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotChanTyDesc)
    decEq a b | (ChanTyDesc type) | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotChanTyDesc)
    decEq a b | (ChanTyDesc type) | (ChanTyDesc x) with (DataTypes.decEq type x)
      decEq a b | (ChanTyDesc type) | (ChanTyDesc x) | (Yes prf) with (prf)
        decEq a b | (ChanTyDesc type) | (ChanTyDesc type) | (Yes prf) | (Same Refl Refl)
          = Yes (Same Refl Refl)
      decEq a b | (ChanTyDesc type) | (ChanTyDesc x) | (No msg contra)
        = No msg (chanTyDescDiffTypes contra)
    decEq a b | (ChanTyDesc type) | (PortTyDesc x dir)
      = No (TypeMismatch a b) chanTyDescNotPortTyDesc
    decEq a b | (ChanTyDesc type) | (NatTyDesc n)
      = No (TypeMismatch a b) chanTyDescNotNatTyDesc
    decEq a b | (ChanTyDesc type) | UnitTyDesc
      = No (TypeMismatch a b) chanTyDescNotUnitTyDesc

  decEq a b | (PortTyDesc type dir) with (b)
    decEq a b | (PortTyDesc type dir) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotPortTyDesc)
    decEq a b | (PortTyDesc type dir) | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotPortTyDesc)
    decEq a b | (PortTyDesc type dir) | (ChanTyDesc x)
      = No (TypeMismatch a b) (negEqSym chanTyDescNotPortTyDesc)
    decEq a b | (PortTyDesc type dir) | (PortTyDesc x y) with (DataTypes.decEq type x)
      decEq a b | (PortTyDesc type dir) | (PortTyDesc x y) | (Yes prf) with (prf)
        decEq a b | (PortTyDesc type dir) | (PortTyDesc type y) | (Yes prf) | (Same Refl Refl) with (Direction.decEq dir y)
          decEq a b | (PortTyDesc type y) | (PortTyDesc type y) | (Yes prf) | (Same Refl Refl) | (Yes Refl)
            = Yes (Same Refl Refl)
          decEq a b | (PortTyDesc type dir) | (PortTyDesc type y) | (Yes prf) | (Same Refl Refl) | (No contra)
            =  No (TypeMismatch a b) (portTyDescDiffDirs contra)
      decEq a b | (PortTyDesc type dir) | (PortTyDesc x y) | (No msg contra)
        = No msg (portTyDescDiffTypes contra)
    decEq a b | (PortTyDesc type dir) | (NatTyDesc n)
      = No (TypeMismatch a b) portTyDescNotNatTyDesc
    decEq a b | (PortTyDesc type dir) | UnitTyDesc
      = No (TypeMismatch a b) portTyDescNotUnitTyDesc

  decEq a b | (NatTyDesc n) with (b)
    decEq a b | (NatTyDesc n) | (FuncTy param return)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotNatTyDesc)
    decEq a b | (NatTyDesc n) | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotNatTyDesc)
    decEq a b | (NatTyDesc n) | (ChanTyDesc type)
      = No (TypeMismatch a b) (negEqSym chanTyDescNotNatTyDesc)
    decEq a b | (NatTyDesc n) | (PortTyDesc type dir)
      = No (TypeMismatch a b) (negEqSym portTyDescNotNatTyDesc)

    decEq a b | (NatTyDesc n) | (NatTyDesc k) with (decEq n k)
      decEq a b | (NatTyDesc k) | (NatTyDesc k) | (Yes Refl)
        = Yes (Same Refl Refl)
      decEq a b | (NatTyDesc n) | (NatTyDesc k) | (No contra)
        = No (TypeMismatch a b) (natTyNatsNotSame contra)

    decEq a b | (NatTyDesc n) | UnitTyDesc
      = No (TypeMismatch a b) natTyDescNotUnitTyDesc

  decEq a b | UnitTyDesc with (b)
    decEq a b | UnitTyDesc | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | (ChanTyDesc type)
      = No (TypeMismatch a b) (negEqSym chanTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | (PortTyDesc type dir)
      = No (TypeMismatch a b) (negEqSym portTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | (NatTyDesc n)
      = No (TypeMismatch a b) (negEqSym natTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | UnitTyDesc
      = Yes (Same Refl Refl)


-- [ EOF ]
