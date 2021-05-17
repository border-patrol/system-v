module SystemV.Annotated.Types.TYPE.Equality.TypeTypes

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Annotated.Types.TYPE
import SystemV.Annotated.Types.TYPE.Equality.Error
import SystemV.Annotated.Types.TYPE.Equality.DataTypes

%default total


funcTypeTyDescNotModuleTyDesc : (Equals Universe TYPE (FuncTy x y) ModuleTyDesc)
                             -> Void
funcTypeTyDescNotModuleTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotChanTyDesc : (Equals Universe TYPE (FuncTy x y) (ChanTyDesc t s i))
                           -> Void
funcTypeTyDescNotChanTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotPortTyDesc : (Equals Universe TYPE (FuncTy x y) (PortTyDesc t d s i))
                           -> Void
funcTypeTyDescNotPortTyDesc (Same Refl Refl) impossible

funcTypeTyDescNotUnitTyDesc : (Equals Universe TYPE (FuncTy x y) UnitTyDesc)
                           -> Void
funcTypeTyDescNotUnitTyDesc (Same Refl Refl) impossible

funcTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                               -> Equals Universe TYPE (FuncTy x a) (FuncTy y b)
                               -> Void
funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

funcTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                -> Equals Universe TYPE (FuncTy x a) (FuncTy x b)
                                -> Void
funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

moduleTyDescNotChanTyDesc : Equals Universe TYPE (ModuleTyDesc) (ChanTyDesc type sense intent) -> Void
moduleTyDescNotChanTyDesc (Same Refl Refl) impossible

moduleTyDescNotPortTyDesc : Equals Universe TYPE (ModuleTyDesc) (PortTyDesc type dir sens intent) -> Void
moduleTyDescNotPortTyDesc (Same Refl Refl) impossible

moduleTyDescNotUnitTyDesc : Equals Universe TYPE (ModuleTyDesc) UnitTyDesc -> Void
moduleTyDescNotUnitTyDesc (Same Refl Refl) impossible

chanTyDescNotPortTyDesc : Equals Universe TYPE (ChanTyDesc type sense intent) (PortTyDesc t d s i) -> Void
chanTyDescNotPortTyDesc (Same Refl Refl) impossible

chanTyDescNotUnitTyDesc : Equals Universe TYPE (ChanTyDesc type sense intent) UnitTyDesc -> Void
chanTyDescNotUnitTyDesc (Same Refl Refl) impossible

chanTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTyDesc x sA iA) (ChanTyDesc y sB iB))
                             -> Void
chanTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

chanTyDescDiffSensitivity : (sense = sB -> Void) -> Equals Universe TYPE (ChanTyDesc type sense intent) (ChanTyDesc type sB iB) -> Void
chanTyDescDiffSensitivity f (Same Refl Refl) = f Refl

chanTyDescDiffIntentions : (intent = iB -> Void) -> Equals Universe TYPE (ChanTyDesc type sB intent) (ChanTyDesc type sB iB) -> Void
chanTyDescDiffIntentions f (Same Refl Refl) = f Refl

portTyDescNotUnitTyDesc : Equals Universe TYPE (PortTyDesc type dir sens intent) UnitTyDesc -> Void
portTyDescNotUnitTyDesc (Same Refl Refl) impossible

portTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTyDesc x ta sa ia) (PortTyDesc y tb sb ib))
                             -> Void
portTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

portTyDescDiffDirs : (contra : a === b -> Void)
                  -> (prf    : Equals Universe TYPE (PortTyDesc x a sa ia) (PortTyDesc x b sb ib))
                            -> Void
portTyDescDiffDirs contra (Same Refl Refl) = contra Refl

portTyDescDiffSensitivity : (sens = sB -> Void) -> Equals Universe TYPE (PortTyDesc type db sens intent) (PortTyDesc type db sB iB) -> Void
portTyDescDiffSensitivity f (Same Refl Refl) = f Refl

portTyDescDiffIntention : (intent = iB -> Void) -> Equals Universe TYPE (PortTyDesc type db sens intent) (PortTyDesc type db sens iB) -> Void
portTyDescDiffIntention f (Same Refl Refl) = f Refl

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
    decEq a b | (FuncTy x y) | (ChanTyDesc type sense intent)
      = No (TypeMismatch a b) (funcTypeTyDescNotChanTyDesc)
    decEq a b | (FuncTy x y) | (PortTyDesc type dir sens intent)
      = No (TypeMismatch a b) (funcTypeTyDescNotPortTyDesc)
    decEq a b | (FuncTy x y) | UnitTyDesc
      = No (TypeMismatch a b) (funcTypeTyDescNotUnitTyDesc)

  decEq a b | ModuleTyDesc with (b)
    decEq a b | ModuleTyDesc | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotModuleTyDesc)
    decEq a b | ModuleTyDesc | ModuleTyDesc
      = Yes (Same Refl Refl)
    decEq a b | ModuleTyDesc | (ChanTyDesc type sense intent)
      = No (TypeMismatch a b) moduleTyDescNotChanTyDesc
    decEq a b | ModuleTyDesc | (PortTyDesc type dir sens intent)
      = No (TypeMismatch a b) moduleTyDescNotPortTyDesc
    decEq a b | ModuleTyDesc | UnitTyDesc
      = No (TypeMismatch a b) moduleTyDescNotUnitTyDesc

  decEq a b | (ChanTyDesc type sense intent) with (b)
    decEq a b | (ChanTyDesc type sense intent) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotChanTyDesc)
    decEq a b | (ChanTyDesc type sense intent) | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotChanTyDesc)
    decEq a b | (ChanTyDesc type sense intent) | (ChanTyDesc tB sB iB) with (DataTypes.decEq type tB)
      decEq a b | (ChanTyDesc type sense intent) | (ChanTyDesc tB sB iB) | (Yes prfWhy) with (prfWhy)
        decEq a b | (ChanTyDesc type sense intent) | (ChanTyDesc type sB iB) | (Yes prfWhy) | (Same Refl Refl) with (decEq sense sB)
          decEq a b | (ChanTyDesc type sB intent) | (ChanTyDesc type sB iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) with (decEq intent iB)
            decEq a b | (ChanTyDesc type sB intent) | (ChanTyDesc type sB intent) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) | (Yes Refl)
              = Yes (Same Refl Refl)
            decEq a b | (ChanTyDesc type sB intent) | (ChanTyDesc type sB iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) | (No contra)
              = No (IntentionMismatch intent iB) (chanTyDescDiffIntentions contra)

          decEq a b | (ChanTyDesc type sense intent) | (ChanTyDesc type sB iB) | (Yes prfWhy) | (Same Refl Refl) | (No contra)
            = No (SensitivityMismatch sense sB) (chanTyDescDiffSensitivity contra)

      decEq a b | (ChanTyDesc type sense intent) | (ChanTyDesc tB sB iB) | (No msgWhyNot prfWhyNot)
        = No msgWhyNot (chanTyDescDiffTypes prfWhyNot)

    decEq a b | (ChanTyDesc type sense intent) | (PortTyDesc t d s i)
      = No (TypeMismatch a b) chanTyDescNotPortTyDesc
    decEq a b | (ChanTyDesc type sense intent) | UnitTyDesc
      = No (TypeMismatch a b) chanTyDescNotUnitTyDesc

  decEq a b | (PortTyDesc type dir sens intent) with (b)
    decEq a b | (PortTyDesc type dir sens intent) | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotPortTyDesc)
    decEq a b | (PortTyDesc type dir sens intent) | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotPortTyDesc)
    decEq a b | (PortTyDesc type dir sens intent) | (ChanTyDesc t s i)
      = No (TypeMismatch a b) (negEqSym chanTyDescNotPortTyDesc)
    decEq a b | (PortTyDesc type dir sens intent) | (PortTyDesc tB db sB iB) with (DataTypes.decEq type tB)
      decEq a b | (PortTyDesc type dir sens intent) | (PortTyDesc tB db sB iB) | (Yes prfWhy) with (prfWhy)
        decEq a b | (PortTyDesc type dir sens intent) | (PortTyDesc type db sB iB) | (Yes prfWhy) | (Same Refl Refl) with (Direction.decEq dir db)
          decEq a b | (PortTyDesc type db sens intent) | (PortTyDesc type db sB iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) with (decEq sens sB)
            decEq a b | (PortTyDesc type db sens intent) | (PortTyDesc type db sens iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) | (Yes Refl) with (decEq intent iB)
              decEq a b | (PortTyDesc type db sens iB) | (PortTyDesc type db sens iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) | (Yes Refl) | (Yes Refl)
                = Yes (Same Refl Refl)
              decEq a b | (PortTyDesc type db sens intent) | (PortTyDesc type db sens iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) | (Yes Refl) | (No contra)
                = No (IntentionMismatch intent iB) (portTyDescDiffIntention contra)
            decEq a b | (PortTyDesc type db sens intent) | (PortTyDesc type db sB iB) | (Yes prfWhy) | (Same Refl Refl) | (Yes Refl) | (No contra)
              = No (SensitivityMismatch sens sB) (portTyDescDiffSensitivity contra)

          decEq a b | (PortTyDesc type dir sens intent) | (PortTyDesc type db sB iB) | (Yes prfWhy) | (Same Refl Refl) | (No contra)
            =  No (TypeMismatch a b) (portTyDescDiffDirs contra)

      decEq a b | (PortTyDesc type dir sens intent) | (PortTyDesc tB db sB iB) | (No msgWhyNot prfWhyNot)
        = No msgWhyNot (portTyDescDiffTypes prfWhyNot)

    decEq a b | (PortTyDesc type dir sens intent) | UnitTyDesc
      = No (TypeMismatch a b) portTyDescNotUnitTyDesc

  decEq a b | UnitTyDesc with (b)
    decEq a b | UnitTyDesc | (FuncTy x y)
      = No (TypeMismatch a b) (negEqSym funcTypeTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | ModuleTyDesc
      = No (TypeMismatch a b) (negEqSym moduleTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | (ChanTyDesc type sense intent)
      = No (TypeMismatch a b) (negEqSym chanTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | (PortTyDesc type dir sens intent)
      = No (TypeMismatch a b) (negEqSym portTyDescNotUnitTyDesc)
    decEq a b | UnitTyDesc | UnitTyDesc
      = Yes (Same Refl Refl)


-- [ EOF ]
