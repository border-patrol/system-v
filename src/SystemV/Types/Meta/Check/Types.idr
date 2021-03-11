module SystemV.Types.Meta.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Utilities

import SystemV.Types.Direction
import SystemV.Types.Meta
import SystemV.Types.Meta.Equality


%default total

||| A predicate to type check types against type formers.
public export
data TyCheck : (type  : MTy (IDX TYPE))
            -> (value : MTy (IDX VALUE))
            -> Type
  where
    ChkModule : TyCheck ModuleTyDesc ModuleVal
    ChkUnit   : TyCheck UnitTy       UnitVal

    ChkFunc : TyCheck         paramTy                   paramValue
           -> TyCheck                 returnTy                     returnValue
           -> TyCheck (FuncTy paramTy returnTy) (FuncTy paramValue returnValue)

    ChkChan  : (Equals Universe Meta typeA typeB) -> TyCheck (ChanTy typeA) (ChanVal typeB)

    ChkPort : (Equals Universe Meta typeA typeB)
           -> (dirA === dirB)
           -> TyCheck (PortTy typeA dirA) (PortVal typeB dirB)

    ChkParam : TyCheck ParamTy ParamVal

data Error = WrongType (MTy (IDX TYPE)) (MTy (IDX VALUE))

funcNoTypeM  : TyCheck (FuncTy x y) ModuleVal -> Void
funcNoTypeM ChkModule impossible
funcNoTypeM ChkUnit impossible
funcNoTypeM (ChkFunc z w) impossible
funcNoTypeM (ChkChan prf) impossible
funcNoTypeM (ChkPort prfTy prfDir) impossible
funcNoTypeM ChkParam impossible

funcNoTypeC  : TyCheck (FuncTy x y) (ChanVal z) -> Void
funcNoTypeC ChkModule impossible
funcNoTypeC ChkUnit impossible
funcNoTypeC (ChkFunc w v) impossible
funcNoTypeC (ChkChan prf) impossible
funcNoTypeC (ChkPort prfTy prfDir) impossible
funcNoTypeC ChkParam impossible

funcNoTypePo : TyCheck (FuncTy x y) (PortVal z dir) -> Void
funcNoTypePo ChkModule impossible
funcNoTypePo ChkUnit impossible
funcNoTypePo (ChkFunc w v) impossible
funcNoTypePo (ChkChan prf) impossible
funcNoTypePo (ChkPort prfTy prfDir) impossible
funcNoTypePo ChkParam impossible

funcNoTypeP  : TyCheck (FuncTy x y) ParamVal -> Void
funcNoTypeP ChkModule impossible
funcNoTypeP ChkUnit impossible
funcNoTypeP (ChkFunc z w) impossible
funcNoTypeP (ChkChan prf) impossible
funcNoTypeP (ChkPort prfTy prfDir) impossible
funcNoTypeP ChkParam impossible

funcNoTypeU  : TyCheck (FuncTy x y) UnitVal -> Void
funcNoTypeU ChkModule impossible
funcNoTypeU ChkUnit impossible
funcNoTypeU (ChkFunc z w) impossible
funcNoTypeU (ChkChan prf) impossible
funcNoTypeU (ChkPort prfTy prfDir) impossible
funcNoTypeU ChkParam impossible

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
modeNoTypeF (ChkChan prf) impossible
modeNoTypeF (ChkPort prfTy prfDir) impossible
modeNoTypeF ChkParam impossible

modeNoTypeC : TyCheck ModuleTyDesc (ChanVal ty) -> Void
modeNoTypeC ChkModule impossible
modeNoTypeC ChkUnit impossible
modeNoTypeC (ChkFunc x y) impossible
modeNoTypeC (ChkChan prf) impossible
modeNoTypeC (ChkPort prfTy prfDir) impossible
modeNoTypeC ChkParam impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortVal ty dir) -> Void
modeNoTypePo ChkModule impossible
modeNoTypePo ChkUnit impossible
modeNoTypePo (ChkFunc x y) impossible
modeNoTypePo (ChkChan prf) impossible
modeNoTypePo (ChkPort prfTy prfDir) impossible
modeNoTypePo ChkParam impossible

modeNoTypeP : TyCheck ModuleTyDesc ParamVal -> Void
modeNoTypeP ChkModule impossible
modeNoTypeP ChkUnit impossible
modeNoTypeP (ChkFunc x y) impossible
modeNoTypeP (ChkChan prf) impossible
modeNoTypeP (ChkPort prfTy prfDir) impossible
modeNoTypeP ChkParam impossible

modeNoTypeU : TyCheck ModuleTyDesc UnitVal -> Void
modeNoTypeU ChkModule impossible
modeNoTypeU ChkUnit impossible
modeNoTypeU (ChkFunc x y) impossible
modeNoTypeU (ChkChan prf) impossible
modeNoTypeU (ChkPort prfTy prfDir) impossible
modeNoTypeU ChkParam impossible

chanNotypeF  : TyCheck (ChanTy type) (FuncTy x y) -> Void
chanNotypeF ChkModule impossible
chanNotypeF ChkUnit impossible
chanNotypeF (ChkFunc z w) impossible
chanNotypeF (ChkChan prf) impossible
chanNotypeF (ChkPort prfTy prfDir) impossible
chanNotypeF ChkParam impossible

chanNotypeM  : TyCheck (ChanTy type) ModuleVal -> Void
chanNotypeM ChkModule impossible
chanNotypeM ChkUnit impossible
chanNotypeM (ChkFunc x y) impossible
chanNotypeM (ChkChan prf) impossible
chanNotypeM (ChkPort prfTy prfDir) impossible
chanNotypeM ChkParam impossible

chanNotypePo : TyCheck (ChanTy type) (PortVal ty dir) -> Void
chanNotypePo ChkModule impossible
chanNotypePo ChkUnit impossible
chanNotypePo (ChkFunc x y) impossible
chanNotypePo (ChkChan prf) impossible
chanNotypePo (ChkPort prfTy prfDir) impossible
chanNotypePo ChkParam impossible

chanNotypeP : TyCheck (ChanTy type) ParamVal -> Void
chanNotypeP ChkModule impossible
chanNotypeP ChkUnit impossible
chanNotypeP (ChkFunc x y) impossible
chanNotypeP (ChkChan prf) impossible
chanNotypeP (ChkPort prfTy prfDir) impossible
chanNotypeP ChkParam impossible

chanNotypeU  : TyCheck (ChanTy type) UnitVal -> Void
chanNotypeU ChkModule impossible
chanNotypeU ChkUnit impossible
chanNotypeU (ChkFunc x y) impossible
chanNotypeU (ChkChan prf) impossible
chanNotypeU (ChkPort prfTy prfDir) impossible
chanNotypeU ChkParam impossible

chanHasWrongType : (contra : Equals Universe Meta x y -> Void)
                -> (prf    : TyCheck (ChanTy x) (ChanVal y))
                          -> Void
chanHasWrongType contra (ChkChan (Same Refl Refl)) = contra (Same Refl Refl)

portNoTypeF : TyCheck (PortTy type dir) (FuncTy x y) -> Void
portNoTypeF ChkModule impossible
portNoTypeF ChkUnit impossible
portNoTypeF (ChkFunc z w) impossible
portNoTypeF (ChkChan z) impossible
portNoTypeF (ChkPort prfTy prfDir) impossible
portNoTypeF ChkParam impossible

portNoTypeM : TyCheck (PortTy type dir) ModuleVal -> Void
portNoTypeM ChkModule impossible
portNoTypeM ChkUnit impossible
portNoTypeM (ChkFunc x y) impossible
portNoTypeM (ChkChan x) impossible
portNoTypeM (ChkPort prfTy prfDir) impossible
portNoTypeM ChkParam impossible

portNoTypeC : TyCheck (PortTy type dir) (ChanVal ty) -> Void
portNoTypeC ChkModule impossible
portNoTypeC ChkUnit impossible
portNoTypeC (ChkFunc x y) impossible
portNoTypeC (ChkChan x) impossible
portNoTypeC (ChkPort prfTy prfDir) impossible
portNoTypeC ChkParam impossible

portNoTypeP : TyCheck (PortTy type dir) ParamVal -> Void
portNoTypeP ChkModule impossible
portNoTypeP ChkUnit impossible
portNoTypeP (ChkFunc x y) impossible
portNoTypeP (ChkChan x) impossible
portNoTypeP (ChkPort prfTy prfDir) impossible
portNoTypeP ChkParam impossible

portNoTypeU : TyCheck (PortTy type dir) UnitVal -> Void
portNoTypeU ChkModule impossible
portNoTypeU ChkUnit impossible
portNoTypeU (ChkFunc x y) impossible
portNoTypeU (ChkChan x) impossible
portNoTypeU (ChkPort prfTy prfDir) impossible
portNoTypeU ChkParam impossible

portWrongType : (contra : Equals Universe Meta ty val -> Void)
             -> (prf    : TyCheck (PortTy ty dirT) (PortVal val dirV))
                       -> Void
portWrongType contra (ChkPort (Same Refl Refl) _) = contra (Same Refl Refl)

portWrongDir : (contra : dirT === dirV -> Void)
            -> (prf    : TyCheck (PortTy ty dirT) (PortVal val dirV))
                      -> Void
portWrongDir contra (ChkPort _ Refl) = contra Refl

paramNotTypeF : TyCheck ParamTy (FuncTy x y) -> Void
paramNotTypeF ChkModule impossible
paramNotTypeF ChkUnit impossible
paramNotTypeF (ChkFunc z w) impossible
paramNotTypeF (ChkChan z) impossible
paramNotTypeF (ChkPort prfTy prfDir) impossible
paramNotTypeF ChkParam impossible

paramNotTypeM : TyCheck ParamTy ModuleVal -> Void
paramNotTypeM ChkModule impossible
paramNotTypeM ChkUnit impossible
paramNotTypeM (ChkFunc x y) impossible
paramNotTypeM (ChkChan x) impossible
paramNotTypeM (ChkPort prfTy prfDir) impossible
paramNotTypeM ChkParam impossible

paramNotTypeC : TyCheck ParamTy (ChanVal x) -> Void
paramNotTypeC ChkModule impossible
paramNotTypeC ChkUnit impossible
paramNotTypeC (ChkFunc y z) impossible
paramNotTypeC (ChkChan y) impossible
paramNotTypeC (ChkPort prfTy prfDir) impossible
paramNotTypeC ChkParam impossible

paramNotTypeP : TyCheck ParamTy (PortVal x dir) -> Void
paramNotTypeP ChkModule impossible
paramNotTypeP ChkUnit impossible
paramNotTypeP (ChkFunc y z) impossible
paramNotTypeP (ChkChan y) impossible
paramNotTypeP (ChkPort prfTy prfDir) impossible
paramNotTypeP ChkParam impossible

paramNotTypeU : TyCheck ParamTy UnitVal -> Void
paramNotTypeU ChkModule impossible
paramNotTypeU ChkUnit impossible
paramNotTypeU (ChkFunc x y) impossible
paramNotTypeU (ChkChan x) impossible
paramNotTypeU (ChkPort prfTy prfDir) impossible
paramNotTypeU ChkParam impossible

unitNoTypeF : TyCheck UnitTy (FuncTy x y) -> Void
unitNoTypeF ChkModule impossible
unitNoTypeF ChkUnit impossible
unitNoTypeF (ChkFunc z w) impossible
unitNoTypeF (ChkChan z) impossible
unitNoTypeF (ChkPort prfTy prfDir) impossible
unitNoTypeF ChkParam impossible

unitNoTypeM : TyCheck UnitTy ModuleVal -> Void
unitNoTypeM ChkModule impossible
unitNoTypeM ChkUnit impossible
unitNoTypeM (ChkFunc x y) impossible
unitNoTypeM (ChkChan x) impossible
unitNoTypeM (ChkPort prfTy prfDir) impossible
unitNoTypeM ChkParam impossible

unitNoTypeC : TyCheck UnitTy (ChanVal t) -> Void
unitNoTypeC ChkModule impossible
unitNoTypeC ChkUnit impossible
unitNoTypeC (ChkFunc x y) impossible
unitNoTypeC (ChkChan x) impossible
unitNoTypeC (ChkPort prfTy prfDir) impossible
unitNoTypeC ChkParam impossible

unitNoTypePo : TyCheck UnitTy (PortVal x dir) -> Void
unitNoTypePo ChkModule impossible
unitNoTypePo ChkUnit impossible
unitNoTypePo (ChkFunc y z) impossible
unitNoTypePo (ChkChan y) impossible
unitNoTypePo (ChkPort prfTy prfDir) impossible
unitNoTypePo ChkParam impossible

unitNoTypeP : TyCheck UnitTy ParamVal -> Void
unitNoTypeP ChkModule impossible
unitNoTypeP ChkUnit impossible
unitNoTypeP (ChkFunc x y) impossible
unitNoTypeP (ChkChan x) impossible
unitNoTypeP (ChkPort prfTy prfDir) impossible
unitNoTypeP ChkParam impossible

export
typeCheck : (type  : MTy (IDX TYPE))
         -> (value : MTy (IDX VALUE))
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

    typeCheck type value | (FuncTy x y) | ModuleVal
      = No (WrongType type value) (funcNoTypeM)
    typeCheck type value | (FuncTy x y) | (ChanVal z)
      = No (WrongType type value) (funcNoTypeC)
    typeCheck type value | (FuncTy x y) | (PortVal z dir)
      = No (WrongType type value) (funcNoTypePo)
    typeCheck type value | (FuncTy x y) | ParamVal
      = No (WrongType type value) (funcNoTypeP)
    typeCheck type value | (FuncTy x y) | UnitVal
      = No (WrongType type value) (funcNoTypeU)

  typeCheck type value | ModuleTyDesc with (value)
    typeCheck type value | ModuleTyDesc | (FuncTy x y)
      = No (WrongType type value) (modeNoTypeF)
    typeCheck type value | ModuleTyDesc | ModuleVal
      = Yes ChkModule
    typeCheck type value | ModuleTyDesc | (ChanVal x)
      = No (WrongType type value) (modeNoTypeC)
    typeCheck type value | ModuleTyDesc | (PortVal x dir)
      = No (WrongType type value) (modeNoTypePo)
    typeCheck type value | ModuleTyDesc | ParamVal
      = No (WrongType type value) (modeNoTypeP)
    typeCheck type value | ModuleTyDesc | UnitVal
      = No (WrongType type value) (modeNoTypeU)

  typeCheck type value | (ChanTy x) with (value)
    typeCheck type value | (ChanTy x) | (FuncTy y z)
      = No (WrongType type value) (chanNotypeF)
    typeCheck type value | (ChanTy x) | ModuleVal
      = No (WrongType type value) (chanNotypeM)

    typeCheck type value | (ChanTy x) | (ChanVal y) with (decEqTypesDataTypes x y)
      typeCheck type value | (ChanTy x) | (ChanVal y) | (Yes prfWhy)
        = Yes (ChkChan prfWhy)
      typeCheck type value | (ChanTy x) | (ChanVal y) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (chanHasWrongType prfWhyNot)

    typeCheck type value | (ChanTy x) | (PortVal y dir)
      = No (WrongType type value) (chanNotypePo)
    typeCheck type value | (ChanTy x) | ParamVal
      = No (WrongType type value) (chanNotypeP)
    typeCheck type value | (ChanTy x) | UnitVal
      = No (WrongType type value) (chanNotypeU)

  typeCheck type value | (PortTy x dir) with (value)
    typeCheck type value | (PortTy x dir) | (FuncTy y z)
      = No (WrongType type value) (portNoTypeF)
    typeCheck type value | (PortTy x dir) | ModuleVal
      = No (WrongType type value) (portNoTypeM)
    typeCheck type value | (PortTy x dir) | (ChanVal y)
      = No (WrongType type value) (portNoTypeC)
    typeCheck type value | (PortTy x dir) | (PortVal y z) with (decEqTypesDataTypes x y)
      typeCheck type value | (PortTy x dir) | (PortVal y z) | (Yes prfWhy) with (Direction.Equality.decEq dir z)
        typeCheck type value | (PortTy x dir) | (PortVal y dir) | (Yes prfWhy) | (Yes Refl)
          = Yes (ChkPort prfWhy Refl)
        typeCheck type value | (PortTy x dir) | (PortVal y z) | (Yes prfWhy) | (No contra)
          = No (WrongType type value) (portWrongDir contra)
      typeCheck type value | (PortTy x dir) | (PortVal y z) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (portWrongType prfWhyNot)
    typeCheck type value | (PortTy x dir) | ParamVal
      = No (WrongType type value) (portNoTypeP)
    typeCheck type value | (PortTy x dir) | UnitVal
      = No (WrongType type value) (portNoTypeU)

  typeCheck type value | ParamTy with (value)
    typeCheck type value | ParamTy | (FuncTy x y)
      = No (WrongType type value) (paramNotTypeF)
    typeCheck type value | ParamTy | ModuleVal
      = No (WrongType type value) (paramNotTypeM)
    typeCheck type value | ParamTy | (ChanVal x)
      = No (WrongType type value) (paramNotTypeC)
    typeCheck type value | ParamTy | (PortVal x dir)
      = No (WrongType type value) (paramNotTypeP)
    typeCheck type value | ParamTy | ParamVal
      = Yes ChkParam
    typeCheck type value | ParamTy | UnitVal
      = No (WrongType type value) (paramNotTypeU)

  typeCheck type value | UnitTy with (value)
    typeCheck type value | UnitTy | (FuncTy x y)
      = No (WrongType type value) (unitNoTypeF)
    typeCheck type value | UnitTy | ModuleVal
      = No (WrongType type value) (unitNoTypeM)
    typeCheck type value | UnitTy | (ChanVal x)
      = No (WrongType type value) (unitNoTypeC)
    typeCheck type value | UnitTy | (PortVal x dir)
      = No (WrongType type value) (unitNoTypePo)
    typeCheck type value | UnitTy | ParamVal
      = No (WrongType type value) (unitNoTypeP)
    typeCheck type value | UnitTy | UnitVal
      = Yes ChkUnit
