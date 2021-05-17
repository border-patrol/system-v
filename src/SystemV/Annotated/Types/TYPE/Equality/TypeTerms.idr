module SystemV.Annotated.Types.TYPE.Equality.TypeTerms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Annotated.Types.TYPE
import SystemV.Annotated.Types.TYPE.Equality.Error
import SystemV.Annotated.Types.TYPE.Equality.DataTypes

%default total

funcTypeTyNotModuleTy : (Equals Universe TYPE (FuncTy x y) ModuleTy)
                             -> Void
funcTypeTyNotModuleTy (Same Refl Refl) impossible

funcTypeTyNotChanTy : (Equals Universe TYPE (FuncTy x y) (ChanTy t s i))
                           -> Void
funcTypeTyNotChanTy (Same Refl Refl) impossible

funcTypeTyNotPortTy : (Equals Universe TYPE (FuncTy x y) (PortTy t d s i))
                           -> Void
funcTypeTyNotPortTy (Same Refl Refl) impossible


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

moduleTyNotChanTy : Equals Universe TYPE (ModuleTy) (ChanTy type sens intent) -> Void
moduleTyNotChanTy (Same Refl Refl) impossible

moduleTyNotPortTy : Equals Universe TYPE (ModuleTy) (PortTy type dir sens intent) -> Void
moduleTyNotPortTy (Same Refl Refl) impossible

moduleTyNotUnitTy : Equals Universe TYPE (ModuleTy) UnitTy -> Void
moduleTyNotUnitTy (Same Refl Refl) impossible

chanTyNotPortTy : Equals Universe TYPE (ChanTy type sens intent) (PortTy t d s i) -> Void
chanTyNotPortTy (Same Refl Refl) impossible

chanTyNotUnitTy : Equals Universe TYPE (ChanTy type sens intent) UnitTy -> Void
chanTyNotUnitTy (Same Refl Refl) impossible

chanTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTy x sens intent) (ChanTy y sb ib))
                             -> Void
chanTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

chanTyDiffSensitivity : (sense = sB -> Void) -> Equals Universe TYPE (ChanTy type sense intent) (ChanTy type sB iB) -> Void
chanTyDiffSensitivity f (Same Refl Refl) = f Refl

chanTyDiffIntention : (intent = iB -> Void) -> Equals Universe TYPE (ChanTy type sB intent) (ChanTy type sB iB) -> Void
chanTyDiffIntention f (Same Refl Refl) = f Refl


portTyNotUnitTy : Equals Universe TYPE (PortTy type dir sens intent) UnitTy -> Void
portTyNotUnitTy (Same Refl Refl) impossible

portTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTy x da sa ia) (PortTy y db sb ib))
                             -> Void
portTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

portTyDiffDirs : (contra : a === b -> Void)
                  -> (prf   : Equals Universe TYPE (PortTy type a sa ia) (PortTy x b sb ib))
                           -> Void
portTyDiffDirs contra (Same Refl Refl) = contra Refl

portTyDiffSensitivity : (sens = sB -> Void) -> Equals Universe TYPE (PortTy type db sens intent) (PortTy type db sB iB) -> Void
portTyDiffSensitivity f (Same Refl Refl) = f Refl

portTyDiffIntention : (intent = iB -> Void) -> Equals Universe TYPE (PortTy type db sens intent) (PortTy type db sens iB) -> Void
portTyDiffIntention f (Same Refl Refl) = f Refl

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
    decEq a b | (FuncTy x y) | (ChanTy type sense intent)
      = No (TypeMismatch a b) (funcTypeTyNotChanTy)
    decEq a b | (FuncTy x y) | (PortTy type dir sens intent)
      = No (TypeMismatch a b) (funcTypeTyNotPortTy)
    decEq a b | (FuncTy x y) | UnitTy
      = No (TypeMismatch a b) (funcTypeTyNotUnitTy)

  decEq a b | ModuleTy with (b)
    decEq a b | ModuleTy | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotModuleTy)
    decEq a b | ModuleTy | ModuleTy
      = Yes (Same Refl Refl)
    decEq a b | ModuleTy | (ChanTy type sense intent)
      = No (TypeMismatch a b) moduleTyNotChanTy
    decEq a b | ModuleTy | (PortTy type dir sens intent)
      = No (TypeMismatch a b) moduleTyNotPortTy
    decEq a b | ModuleTy | UnitTy
      = No (TypeMismatch a b) moduleTyNotUnitTy

  decEq a b | (ChanTy type sense intent) with (b)
    decEq a b | (ChanTy type sense intent) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotChanTy)
    decEq a b | (ChanTy type sense intent) | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotChanTy)
    decEq a b | (ChanTy type sense intent) | (ChanTy tb sb ib) with (DataTypes.decEq type tb)
      decEq a b | (ChanTy type sense intent) | (ChanTy tb sb ib) | (Yes prf) with (prf)
        decEq a b | (ChanTy type sense intent) | (ChanTy type sb ib) | (Yes prf) | (Same Refl Refl) with (decEq sense sb)
          decEq a b | (ChanTy type sb intent) | (ChanTy type sb ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) with (decEq intent ib)
            decEq a b | (ChanTy type sb intent) | (ChanTy type sb intent) | (Yes prf) | (Same Refl Refl) | (Yes Refl) | (Yes Refl)
              = Yes (Same Refl Refl)
            decEq a b | (ChanTy type sb intent) | (ChanTy type sb ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) | (No contra)
              = No (IntentionMismatch intent ib) (chanTyDiffIntention contra)
          decEq a b | (ChanTy type sense intent) | (ChanTy type sb ib) | (Yes prf) | (Same Refl Refl) | (No contra)
            = No (SensitivityMismatch sense sb) (chanTyDiffSensitivity contra)
      decEq a b | (ChanTy type sense intent) | (ChanTy x sb ib) | (No msg contra)
        = No msg (chanTyDiffTypes contra)
    decEq a b | (ChanTy type sense intent) | (PortTy t d s i)
      = No (TypeMismatch a b) chanTyNotPortTy
    decEq a b | (ChanTy type sense intent) | UnitTy
      = No (TypeMismatch a b) chanTyNotUnitTy

  decEq a b | (PortTy type dir sens intent) with (b)
    decEq a b | (PortTy type dir sens intent) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotPortTy)
    decEq a b | (PortTy type dir sens intent) | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotPortTy)
    decEq a b | (PortTy type dir sens intent) | (ChanTy t s i)
      = No (TypeMismatch a b) (negEqSym chanTyNotPortTy)
    decEq a b | (PortTy type dir sens intent) | (PortTy tb db sb ib) with (DataTypes.decEq type tb)
      decEq a b | (PortTy type dir sens intent) | (PortTy tb db sb ib) | (Yes prf) with (prf)
        decEq a b | (PortTy type dir sens intent) | (PortTy type db sb ib) | (Yes prf) | (Same Refl Refl) with (Direction.decEq dir db)
          decEq a b | (PortTy type dir sens intent) | (PortTy type dir sb ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) with (decEq sens sb)
            decEq a b | (PortTy type dir sens intent) | (PortTy type dir sens ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) | (Yes Refl) with (decEq intent ib)
              decEq a b | (PortTy type dir sens ib) | (PortTy type dir sens ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl)
                = Yes (Same Refl Refl)
              decEq a b | (PortTy type dir sens intent) | (PortTy type dir sens ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) | (Yes Refl) | (No contra)
                = No (TypeMismatch a b) (portTyDiffIntention contra)
            decEq a b | (PortTy type dir sens intent) | (PortTy type dir sb ib) | (Yes prf) | (Same Refl Refl) | (Yes Refl) | (No contra)
              = No (TypeMismatch a b) (portTyDiffSensitivity contra)
          decEq a b | (PortTy type dir sens intent) | (PortTy type db sb ib) | (Yes prf) | (Same Refl Refl) | (No contra)
            = No (TypeMismatch a b) (portTyDiffDirs contra)
      decEq a b | (PortTy type dir sens intent) | (PortTy tb db sb ib) | (No msg contra)
        = No msg (portTyDiffTypes contra)
    decEq a b | (PortTy type dir sens intent) | UnitTy
      = No (TypeMismatch a b) portTyNotUnitTy

  decEq a b | UnitTy with (b)
    decEq a b | UnitTy | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyNotUnitTy)
    decEq a b | UnitTy | ModuleTy
      = No (TypeMismatch a b) (negEqSym moduleTyNotUnitTy)
    decEq a b | UnitTy | (ChanTy type sense intent)
      = No (TypeMismatch a b) (negEqSym chanTyNotUnitTy)
    decEq a b | UnitTy | (PortTy type dir sens intent)
      = No (TypeMismatch a b) (negEqSym portTyNotUnitTy)
    decEq a b | UnitTy | UnitTy = Yes (Same Refl Refl)


-- [ EOF ]
