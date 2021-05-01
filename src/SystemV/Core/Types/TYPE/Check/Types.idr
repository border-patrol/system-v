module SystemV.Core.Types.TYPE.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Core.Types.TYPE
import SystemV.Core.Types.TYPE.Equality


%default total

||| A predicate to type check types against type formers.
public export
data TyCheck : (type  : TYPE (IDX TYPE))
            -> (value : TYPE (IDX TERM))
            -> Type
  where
    ChkModule : TyCheck ModuleTyDesc  ModuleTy
    ChkUnit   : TyCheck UnitTyDesc    UnitTy

    ChkFunc : TyCheck         paramTy                   paramValue
           -> TyCheck                 returnTy                     returnValue
           -> TyCheck (FuncTy paramTy returnTy) (FuncTy paramValue returnValue)

    ChkChan  : (Equals Universe TYPE typeA typeB)
           -> TyCheck (ChanTyDesc typeA) (ChanTy typeB)

    ChkPort : (Equals Universe TYPE typeA typeB)
           -> (dirA === dirB)
           -> TyCheck (PortTyDesc typeA dirA) (PortTy typeB dirB)

public export
data Error = WrongType (TYPE (IDX TYPE)) (TYPE (IDX TERM))

funcNoTypeM  : TyCheck (FuncTy x y) ModuleTy -> Void
funcNoTypeM ChkModule impossible
funcNoTypeM ChkUnit impossible
funcNoTypeM (ChkFunc z w) impossible
funcNoTypeM (ChkChan z) impossible
funcNoTypeM (ChkPort z prf) impossible

funcNoTypeC  : TyCheck (FuncTy x y) (ChanTy z) -> Void
funcNoTypeC ChkModule impossible
funcNoTypeC ChkUnit impossible
funcNoTypeC (ChkFunc w v) impossible
funcNoTypeC (ChkChan w) impossible
funcNoTypeC (ChkPort w prf) impossible

funcNoTypePo : TyCheck (FuncTy x y) (PortTy z dir) -> Void
funcNoTypePo ChkModule impossible
funcNoTypePo ChkUnit impossible
funcNoTypePo (ChkFunc w v) impossible
funcNoTypePo (ChkChan w) impossible
funcNoTypePo (ChkPort w prf) impossible

funcNoTypeU  : TyCheck (FuncTy x y) UnitTy -> Void
funcNoTypeU ChkModule impossible
funcNoTypeU ChkUnit impossible
funcNoTypeU (ChkFunc z w) impossible
funcNoTypeU (ChkChan z) impossible
funcNoTypeU (ChkPort z prf) impossible

funcNoTyCheckParam : (contra : TyCheck ty val -> Void)
                  -> (prf    : TyCheck (FuncTy ty rty) (FuncTy val rval))
                            -> Void
funcNoTyCheckParam contra (ChkFunc x y) = contra x

funcNoTyCheckRet : (contra : TyCheck rty rval -> Void)
                -> (prf    : TyCheck (FuncTy ty rty) (FuncTy val rval))
                          -> Void
funcNoTyCheckRet contra (ChkFunc x y) = contra y

modeNoTypeF : TyCheck ModuleTyDesc (FuncTy x y) -> Void
modeNoTypeF ChkModule impossible
modeNoTypeF ChkUnit impossible
modeNoTypeF (ChkFunc z w) impossible
modeNoTypeF (ChkChan z) impossible
modeNoTypeF (ChkPort z prf) impossible

modeNoTypeC : TyCheck ModuleTyDesc (ChanTy ty) -> Void
modeNoTypeC ChkModule impossible
modeNoTypeC ChkUnit impossible
modeNoTypeC (ChkFunc x y) impossible
modeNoTypeC (ChkChan x) impossible
modeNoTypeC (ChkPort x prf) impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortTy ty dir) -> Void
modeNoTypePo ChkModule impossible
modeNoTypePo ChkUnit impossible
modeNoTypePo (ChkFunc x y) impossible
modeNoTypePo (ChkChan x) impossible
modeNoTypePo (ChkPort x prf) impossible

modeNoTypeU : TyCheck ModuleTyDesc UnitTy -> Void
modeNoTypeU ChkModule impossible
modeNoTypeU ChkUnit impossible
modeNoTypeU (ChkFunc x y) impossible
modeNoTypeU (ChkChan x) impossible
modeNoTypeU (ChkPort x prf) impossible

chanNotypeF : TyCheck (ChanTyDesc type) (FuncTy x y) -> Void
chanNotypeF ChkModule impossible
chanNotypeF ChkUnit impossible
chanNotypeF (ChkFunc z w) impossible
chanNotypeF (ChkChan z) impossible
chanNotypeF (ChkPort z prf) impossible

chanNotypeM  : TyCheck (ChanTyDesc type) ModuleTy -> Void
chanNotypeM ChkModule impossible
chanNotypeM ChkUnit impossible
chanNotypeM (ChkFunc x y) impossible
chanNotypeM (ChkChan x) impossible
chanNotypeM (ChkPort x prf) impossible

chanNotypePo : TyCheck (ChanTyDesc type) (PortTy ty dir) -> Void
chanNotypePo ChkModule impossible
chanNotypePo ChkUnit impossible
chanNotypePo (ChkFunc x y) impossible
chanNotypePo (ChkChan x) impossible
chanNotypePo (ChkPort x prf) impossible

chanNotypeU  : TyCheck (ChanTyDesc type) UnitTy -> Void
chanNotypeU ChkModule impossible
chanNotypeU ChkUnit impossible
chanNotypeU (ChkFunc x y) impossible
chanNotypeU (ChkChan x) impossible
chanNotypeU (ChkPort x prf) impossible

chanHasWrongType : (contra : Equals Universe TYPE x y -> Void)
                -> (prf    : TyCheck (ChanTyDesc x) (ChanTy y))
                          -> Void
chanHasWrongType contra (ChkChan (Same Refl Refl)) = contra (Same Refl Refl)

portNoTypeF : TyCheck (PortTyDesc type dir) (FuncTy x y) -> Void
portNoTypeF ChkModule impossible
portNoTypeF ChkUnit impossible
portNoTypeF (ChkFunc z w) impossible
portNoTypeF (ChkChan z) impossible
portNoTypeF (ChkPort z prf) impossible

portNoTypeM : TyCheck (PortTyDesc type dir) ModuleTy -> Void
portNoTypeM ChkModule impossible
portNoTypeM ChkUnit impossible
portNoTypeM (ChkFunc x y) impossible
portNoTypeM (ChkChan x) impossible
portNoTypeM (ChkPort x prf) impossible

portNoTypeC : TyCheck (PortTyDesc type dir) (ChanTy ty) -> Void
portNoTypeC ChkModule impossible
portNoTypeC ChkUnit impossible
portNoTypeC (ChkFunc x y) impossible
portNoTypeC (ChkChan x) impossible
portNoTypeC (ChkPort x prf) impossible

portNoTypeU : TyCheck (PortTyDesc type dir) UnitTy -> Void
portNoTypeU ChkModule impossible
portNoTypeU ChkUnit impossible
portNoTypeU (ChkFunc x y) impossible
portNoTypeU (ChkChan x) impossible
portNoTypeU (ChkPort x prf) impossible


portWrongType : (contra : Equals Universe TYPE ty val -> Void)
             -> (prf    : TyCheck (PortTyDesc ty dirT) (PortTy val dirV))
                       -> Void
portWrongType contra (ChkPort (Same Refl Refl) _) = contra (Same Refl Refl)

portWrongDir : (contra : dirT === dirV -> Void)
            -> (prf    : TyCheck (PortTyDesc ty dirT) (PortTy val dirV))
                      -> Void
portWrongDir contra (ChkPort _ Refl) = contra Refl

unitNoTypeF : TyCheck UnitTyDesc (FuncTy x y) -> Void
unitNoTypeF ChkModule impossible
unitNoTypeF ChkUnit impossible
unitNoTypeF (ChkFunc z w) impossible
unitNoTypeF (ChkChan z) impossible
unitNoTypeF (ChkPort z prf) impossible

unitNoTypeM : TyCheck UnitTyDesc ModuleTy -> Void
unitNoTypeM ChkModule impossible
unitNoTypeM ChkUnit impossible
unitNoTypeM (ChkFunc x y) impossible
unitNoTypeM (ChkChan x) impossible
unitNoTypeM (ChkPort x prf) impossible

unitNoTypeC : TyCheck UnitTyDesc (ChanTy t) -> Void
unitNoTypeC ChkModule impossible
unitNoTypeC ChkUnit impossible
unitNoTypeC (ChkFunc x y) impossible
unitNoTypeC (ChkChan x) impossible
unitNoTypeC (ChkPort x prf) impossible

unitNoTypePo : TyCheck UnitTyDesc (PortTy x dir) -> Void
unitNoTypePo ChkModule impossible
unitNoTypePo ChkUnit impossible
unitNoTypePo (ChkFunc y z) impossible
unitNoTypePo (ChkChan y) impossible
unitNoTypePo (ChkPort y prf) impossible


export
typeCheck : (type  : TYPE (IDX TYPE))
         -> (value : TYPE (IDX TERM))
                  -> DecInfo Types.Error (TyCheck type value)
typeCheck type value with (type)
  typeCheck type value | (FuncTy x y) with (value)
    typeCheck type value | (FuncTy x y) | (FuncTy z w) with (typeCheck x z)
      typeCheck type value | (FuncTy x y) | (FuncTy z w) | (Yes prfWhy) with (typeCheck y w)
        typeCheck type value | (FuncTy x y) | (FuncTy z w) | (Yes prfWhy) | (Yes v)
          = Yes (ChkFunc prfWhy v)
        typeCheck type value | (FuncTy x y) | (FuncTy z w) | (Yes prfWhy) | (No msgWhyNot prfWhyNot)
          = No (WrongType type value) (funcNoTyCheckRet prfWhyNot)
      typeCheck type value | (FuncTy x y) | (FuncTy z w) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (funcNoTyCheckParam prfWhyNot)

    typeCheck type value | (FuncTy x y) | ModuleTy
      = No (WrongType type value) (funcNoTypeM)
    typeCheck type value | (FuncTy x y) | (ChanTy z)
      = No (WrongType type value) (funcNoTypeC)
    typeCheck type value | (FuncTy x y) | (PortTy z dir)
      = No (WrongType type value) (funcNoTypePo)
    typeCheck type value | (FuncTy x y) | UnitTy
      = No (WrongType type value) (funcNoTypeU)

  typeCheck type value | ModuleTyDesc with (value)
    typeCheck type value | ModuleTyDesc | (FuncTy x y)
      = No (WrongType type value) (modeNoTypeF)
    typeCheck type value | ModuleTyDesc | ModuleTy
      = Yes ChkModule
    typeCheck type value | ModuleTyDesc | (ChanTy x)
      = No (WrongType type value) (modeNoTypeC)
    typeCheck type value | ModuleTyDesc | (PortTy x dir)
      = No (WrongType type value) (modeNoTypePo)
    typeCheck type value | ModuleTyDesc | UnitTy
      = No (WrongType type value) (modeNoTypeU)

  typeCheck type value | (ChanTyDesc x) with (value)
    typeCheck type value | (ChanTyDesc x) | (FuncTy y z)
      = No (WrongType type value) (chanNotypeF)
    typeCheck type value | (ChanTyDesc x) | ModuleTy
      = No (WrongType type value) (chanNotypeM)

    typeCheck type value | (ChanTyDesc x) | (ChanTy y) with (DataTypes.decEq x y)
      typeCheck type value | (ChanTyDesc x) | (ChanTy y) | (Yes prfWhy)
        = Yes (ChkChan prfWhy)
      typeCheck type value | (ChanTyDesc x) | (ChanTy y) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (chanHasWrongType prfWhyNot)

    typeCheck type value | (ChanTyDesc x) | (PortTy y dir)
      = No (WrongType type value) (chanNotypePo)
    typeCheck type value | (ChanTyDesc x) | UnitTy
      = No (WrongType type value) (chanNotypeU)

  typeCheck type value | (PortTyDesc x dir) with (value)
    typeCheck type value | (PortTyDesc x dir) | (FuncTy y z)
      = No (WrongType type value) (portNoTypeF)
    typeCheck type value | (PortTyDesc x dir) | ModuleTy
      = No (WrongType type value) (portNoTypeM)
    typeCheck type value | (PortTyDesc x dir) | (ChanTy y)
      = No (WrongType type value) (portNoTypeC)
    typeCheck type value | (PortTyDesc x dir) | (PortTy y z) with (DataTypes.decEq x y)
      typeCheck type value | (PortTyDesc x dir) | (PortTy y z) | (Yes prfWhy) with (Direction.decEq dir z)
        typeCheck type value | (PortTyDesc x dir) | (PortTy y dir) | (Yes prfWhy) | (Yes Refl)
          = Yes (ChkPort prfWhy Refl)
        typeCheck type value | (PortTyDesc x dir) | (PortTy y z) | (Yes prfWhy) | (No contra)
          = No (WrongType type value) (portWrongDir contra)
      typeCheck type value | (PortTyDesc x dir) | (PortTy y z) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (portWrongType prfWhyNot)
    typeCheck type value | (PortTyDesc x dir) | UnitTy
      = No (WrongType type value) (portNoTypeU)

  typeCheck type value | UnitTyDesc with (value)
    typeCheck type value | UnitTyDesc | (FuncTy x y)
      = No (WrongType type value) (unitNoTypeF)
    typeCheck type value | UnitTyDesc | ModuleTy
      = No (WrongType type value) (unitNoTypeM)
    typeCheck type value | UnitTyDesc | (ChanTy x)
      = No (WrongType type value) (unitNoTypeC)
    typeCheck type value | UnitTyDesc | (PortTy x dir)
      = No (WrongType type value) (unitNoTypePo)
    typeCheck type value | UnitTyDesc | UnitTy
      = Yes ChkUnit
