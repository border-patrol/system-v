module SystemV.Param.Types.TYPE.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Param.Types.TYPE
import SystemV.Param.Types.TYPE.Equality

import SystemV.Param.Types.TYPE.Equality.DataTerms

%default total

||| A predicate to type check types against type formers.
public export
data TyCheck : (type  : TYPE (IDX TYPE))
            -> (value : TYPE (IDX TERM))
            -> Type
  where
    ChkModule : TyCheck ModuleTyDesc  ModuleTy
    ChkUnit   : TyCheck UnitTyDesc    UnitTy

    ChkNat    : TyCheck NatTyDesc     NatTy

    ChkBool   : TyCheck BoolTyDesc BoolTy

--    ChkFuncDef : TyCheck              paramTy                       paramValue
--              -> TyCheck                      returnTy                          returnValue
--              -> TyCheck (FuncParamTy u paramTy returnTy) (FuncParamTy u paramValue returnValue)
--
--
--    ChkFunc : TyCheck         paramTy                   paramValue
--           -> TyCheck                 returnTy                     returnValue
--           -> TyCheck (FuncTy paramTy returnTy) (FuncTy paramValue returnValue)

    ChkChan  : (Equals Universe TYPE typeA typeB)
           -> TyCheck (ChanTyDesc typeA) (ChanTy typeB)

    ChkPort : (Equals Universe TYPE typeA typeB)
           -> (dirA === dirB)
           -> TyCheck (PortTyDesc typeA dirA) (PortTy typeB dirB)

public export
data Error = WrongType (TYPE (IDX TYPE)) (TYPE (IDX TERM))

-- ## Function Voids

funcNoTypeM  : TyCheck (FuncTy x y) ModuleTy -> Void
funcNoTypeM ChkModule impossible

funcNoTypeC  : TyCheck (FuncTy x y) (ChanTy z) -> Void
funcNoTypeC ChkModule impossible


funcNoTypePo : TyCheck (FuncTy x y) (PortTy z dir) -> Void
funcNoTypePo ChkModule impossible

funcNoTypeN : TyCheck (FuncTy x y) (NatTy) -> Void
funcNoTypeN ChkModule impossible


funcNoTypeU  : TyCheck (FuncTy x y) UnitTy -> Void
funcNoTypeU ChkModule impossible


funcNoTypeB  : TyCheck (FuncTy x y) BoolTy -> Void
funcNoTypeB ChkModule impossible


--funcNoTyCheckParam : (contra : TyCheck ty val -> Void)
--                  -> (prf    : TyCheck (FuncTy ty rty) (FuncTy val rval))
--                            -> Void
--funcNoTyCheckParam contra (ChkFunc x y) = contra x
--
--funcNoTyCheckRet : (contra : TyCheck rty rval -> Void)
--                -> (prf    : TyCheck (FuncTy ty rty) (FuncTy val rval))
--                          -> Void
--funcNoTyCheckRet contra (ChkFunc x y) = contra y

funcNoTypeFD : TyCheck (FuncTy x y) (FuncParamTy u a r) -> Void
funcNoTypeFD ChkModule impossible

-- ## Function Defaults Voids

funcDefNoTypeM  : TyCheck (FuncParamTy u x y) ModuleTy -> Void
funcDefNoTypeM ChkModule impossible


funcDefNoTypeC  : TyCheck (FuncParamTy u x y) (ChanTy z) -> Void
funcDefNoTypeC ChkModule impossible


funcDefNoTypePo : TyCheck (FuncParamTy u x y) (PortTy z dir) -> Void
funcDefNoTypePo ChkModule impossible


funcDefNoTypeN : TyCheck (FuncParamTy u x y) (NatTy) -> Void
funcDefNoTypeN ChkModule impossible

funcDefNoTypeU  : TyCheck (FuncParamTy u x y) UnitTy -> Void
funcDefNoTypeU ChkModule impossible


funcDefNoTypeB  : TyCheck (FuncParamTy u x y) BoolTy -> Void
funcDefNoTypeB ChkModule impossible


--funcDefNoTyCheckParam : (contra : TyCheck ty val -> Void)
--                     -> (prf    : TyCheck (FuncParamTy ty rty) (FuncParamTy val rval))
--                               -> Void
--funcDefNoTyCheckParam contra (ChkFuncDef x y) = contra x
--
--funcDefNoTyCheckRet : (contra : TyCheck rty rval -> Void)
--                   -> (prf    : TyCheck (FuncParamTy ty rty) (FuncParamTy val rval))
--                             -> Void
--funcDefNoTyCheckRet contra (ChkFuncDef x y) = contra y

funcDefNoTypeF : TyCheck (FuncParamTy u x y) (FuncTy a r) -> Void
funcDefNoTypeF ChkModule impossible

-- ## Modules

modeNoTypeF : TyCheck ModuleTyDesc (FuncTy x y) -> Void
modeNoTypeF ChkModule impossible

modeNoTypeFD : TyCheck ModuleTyDesc (FuncParamTy u x y) -> Void
modeNoTypeFD ChkModule impossible

modeNoTypeC : TyCheck ModuleTyDesc (ChanTy ty) -> Void
modeNoTypeC ChkModule impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortTy ty dir) -> Void
modeNoTypePo ChkModule impossible

modeNoTypeN : TyCheck ModuleTyDesc (NatTy) -> Void
modeNoTypeN ChkModule impossible


modeNoTypeU : TyCheck ModuleTyDesc UnitTy -> Void
modeNoTypeU ChkModule impossible


modeNoTypeB : TyCheck ModuleTyDesc BoolTy -> Void
modeNoTypeB ChkModule impossible


-- ## Channels

chanNotypeF : TyCheck (ChanTyDesc type) (FuncTy x y) -> Void
chanNotypeF ChkModule impossible


chanNotypeFD : TyCheck (ChanTyDesc type) (FuncParamTy u x y) -> Void
chanNotypeFD ChkModule impossible

chanNotypeM  : TyCheck (ChanTyDesc type) ModuleTy -> Void
chanNotypeM ChkModule impossible

chanNotypePo : TyCheck (ChanTyDesc type) (PortTy ty dir) -> Void
chanNotypePo ChkModule impossible

chanNotypeN : TyCheck (ChanTyDesc x) (NatTy) -> Void
chanNotypeN ChkModule impossible

chanNotypeU  : TyCheck (ChanTyDesc type) UnitTy -> Void
chanNotypeU ChkModule impossible


chanNotypeB  : TyCheck (ChanTyDesc type) BoolTy -> Void
chanNotypeB ChkModule impossible


chanHasWrongType : (contra : Equals Universe TYPE x y -> Void)
                -> (prf    : TyCheck (ChanTyDesc x) (ChanTy y))
                          -> Void
chanHasWrongType contra (ChkChan (Same Refl Refl)) = contra (Same Refl Refl)


-- ## Ports

portNoTypeF : TyCheck (PortTyDesc type dir) (FuncTy x y) -> Void
portNoTypeF ChkModule impossible

portNoTypeFD : TyCheck (PortTyDesc type dir) (FuncParamTy u x y) -> Void
portNoTypeFD ChkModule impossible

portNoTypeM : TyCheck (PortTyDesc type dir) ModuleTy -> Void
portNoTypeM ChkModule impossible


portNoTypeC : TyCheck (PortTyDesc type dir) (ChanTy ty) -> Void
portNoTypeC ChkModule impossible


portNoTypeN : TyCheck (PortTyDesc x dir) NatTy -> Void
portNoTypeN ChkModule impossible


portNoTypeU : TyCheck (PortTyDesc type dir) UnitTy -> Void
portNoTypeU ChkModule impossible


portNoTypeB : TyCheck (PortTyDesc type dir) BoolTy -> Void
portNoTypeB ChkModule impossible

portWrongType : (contra : Equals Universe TYPE ty val -> Void)
             -> (prf    : TyCheck (PortTyDesc ty dirT) (PortTy val dirV))
                       -> Void
portWrongType contra (ChkPort (Same Refl Refl) _) = contra (Same Refl Refl)

portWrongDir : (contra : dirT === dirV -> Void)
            -> (prf    : TyCheck (PortTyDesc ty dirT) (PortTy val dirV))
                      -> Void
portWrongDir contra (ChkPort _ Refl) = contra Refl

-- ## Nats

natNoTypeF : TyCheck (NatTyDesc) (FuncTy param return) -> Void
natNoTypeF ChkModule impossible

natNoTypeFD : TyCheck (NatTyDesc) (FuncParamTy u param return) -> Void
natNoTypeFD ChkModule impossible


natNoTypeC : TyCheck (NatTyDesc) (ChanTy x) -> Void
natNoTypeC ChkModule impossible


natNoTypeM : TyCheck (NatTyDesc) ModuleTy -> Void
natNoTypeM ChkModule impossible


natNoTypeP : TyCheck (NatTyDesc) (PortTy x dir) -> Void
natNoTypeP ChkModule impossible


natNoTypeU : TyCheck (NatTyDesc) UnitTy -> Void
natNoTypeU ChkModule impossible


natNoTypeB : TyCheck (NatTyDesc) BoolTy -> Void
natNoTypeB ChkModule impossible


-- ## Unit

unitNoTypeF : TyCheck UnitTyDesc (FuncTy x y) -> Void
unitNoTypeF ChkModule impossible


unitNoTypeFD : TyCheck UnitTyDesc (FuncParamTy u x y) -> Void
unitNoTypeFD ChkModule impossible

unitNoTypeM : TyCheck UnitTyDesc ModuleTy -> Void
unitNoTypeM ChkModule impossible


unitNoTypeC : TyCheck UnitTyDesc (ChanTy t) -> Void
unitNoTypeC ChkModule impossible

unitNoTypePo : TyCheck UnitTyDesc (PortTy x dir) -> Void
unitNoTypePo ChkModule impossible

unitNoTypeN : TyCheck UnitTyDesc NatTy -> Void
unitNoTypeN ChkModule impossible

unitNoTypeB : TyCheck UnitTyDesc BoolTy -> Void
unitNoTypeB ChkModule impossible

-- ## Booleans

boolNoTypeF : TyCheck BoolTyDesc (FuncTy x y) -> Void
boolNoTypeF ChkModule impossible

boolNoTypeFD : TyCheck BoolTyDesc (FuncParamTy u x y) -> Void
boolNoTypeFD ChkModule impossible

boolNoTypeM : TyCheck BoolTyDesc ModuleTy -> Void
boolNoTypeM ChkModule impossible



boolNoTypeU : TyCheck BoolTyDesc UnitTy -> Void
boolNoTypeU ChkModule impossible


boolNoTypeC : TyCheck BoolTyDesc (ChanTy t) -> Void
boolNoTypeC ChkModule impossible

boolNoTypePo : TyCheck BoolTyDesc (PortTy x dir) -> Void
boolNoTypePo ChkModule impossible


boolNoTypeN : TyCheck BoolTyDesc NatTy -> Void
boolNoTypeN ChkModule impossible


-- ## Func Def
func : TyCheck (FuncTy x y) (FuncTy z w) -> Void
func ChkModule impossible

funcParam : TyCheck (FuncParamTy u x y) (FuncParamTy i z w) -> Void
funcParam ChkModule impossible

-- ## Type Checking

export
typeCheck : (type  : TYPE (IDX TYPE))
         -> (value : TYPE (IDX TERM))
                  -> DecInfo Types.Error (TyCheck type value)
typeCheck type value with (type)
  typeCheck type value | (FuncTy x y) with (value)
    typeCheck type value | (FuncTy x y) | (FuncTy z w)
      = No (WrongType type value) func
    typeCheck type value | (FuncTy x y) | ModuleTy
      = No (WrongType type value) (funcNoTypeM)
    typeCheck type value | (FuncTy x y) | (ChanTy z)
      = No (WrongType type value) (funcNoTypeC)
    typeCheck type value | (FuncTy x y) | (PortTy z dir)
      = No (WrongType type value) (funcNoTypePo)
    typeCheck type value | (FuncTy x y) | NatTy
      = No (WrongType type value) (funcNoTypeN)
    typeCheck type value | (FuncTy x y) | UnitTy
      = No (WrongType type value) (funcNoTypeU)

    typeCheck type value | (FuncTy x y) | BoolTy
      = No (WrongType type value) (funcNoTypeB)

    typeCheck type value | (FuncTy x y) | (FuncParamTy u a r)
      = No (WrongType type value) (funcNoTypeFD)

  typeCheck type value | ModuleTyDesc with (value)
    typeCheck type value | ModuleTyDesc | (FuncTy x y)
      = No (WrongType type value) (modeNoTypeF)
    typeCheck type value | ModuleTyDesc | ModuleTy
      = Yes ChkModule
    typeCheck type value | ModuleTyDesc | (ChanTy x)
      = No (WrongType type value) (modeNoTypeC)
    typeCheck type value | ModuleTyDesc | (PortTy x dir)
      = No (WrongType type value) (modeNoTypePo)
    typeCheck type value | ModuleTyDesc | NatTy
      = No (WrongType type value) (modeNoTypeN)
    typeCheck type value | ModuleTyDesc | UnitTy
      = No (WrongType type value) (modeNoTypeU)
    typeCheck type value | ModuleTyDesc | BoolTy
      = No (WrongType type value) (modeNoTypeB)
    typeCheck type value | ModuleTyDesc | (FuncParamTy u a r)
      = No (WrongType type value) (modeNoTypeFD)

  typeCheck type value | (ChanTyDesc x) with (value)
    typeCheck type value | (ChanTyDesc x) | (FuncTy y z)
      = No (WrongType type value) (chanNotypeF)
    typeCheck type value | (ChanTyDesc x) | ModuleTy
      = No (WrongType type value) (chanNotypeM)

    typeCheck type value | (ChanTyDesc x) | (ChanTy y) with (DataTerms.decEq x y)
      typeCheck type value | (ChanTyDesc x) | (ChanTy y) | (Yes prfWhy)
        = Yes (ChkChan prfWhy)
      typeCheck type value | (ChanTyDesc x) | (ChanTy y) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (chanHasWrongType prfWhyNot)

    typeCheck type value | (ChanTyDesc x) | (PortTy y dir)
      = No (WrongType type value) (chanNotypePo)
    typeCheck type value | (ChanTyDesc x) | NatTy
      = No (WrongType type value) (chanNotypeN)
    typeCheck type value | (ChanTyDesc x) | UnitTy
      = No (WrongType type value) (chanNotypeU)
    typeCheck type value | (ChanTyDesc x) | BoolTy
      = No (WrongType type value) (chanNotypeB)
    typeCheck type value | (ChanTyDesc x) | (FuncParamTy u a r)
      = No (WrongType type value) (chanNotypeFD)

  typeCheck type value | (PortTyDesc x dir) with (value)
    typeCheck type value | (PortTyDesc x dir) | (FuncTy y z)
      = No (WrongType type value) (portNoTypeF)
    typeCheck type value | (PortTyDesc x dir) | ModuleTy
      = No (WrongType type value) (portNoTypeM)
    typeCheck type value | (PortTyDesc x dir) | (ChanTy y)
      = No (WrongType type value) (portNoTypeC)
    typeCheck type value | (PortTyDesc x dir) | (PortTy y z) with (DataTerms.decEq x y)
      typeCheck type value | (PortTyDesc x dir) | (PortTy y z) | (Yes prfWhy) with (Direction.decEq dir z)
        typeCheck type value | (PortTyDesc x dir) | (PortTy y dir) | (Yes prfWhy) | (Yes Refl)
          = Yes (ChkPort prfWhy Refl)
        typeCheck type value | (PortTyDesc x dir) | (PortTy y z) | (Yes prfWhy) | (No contra)
          = No (WrongType type value) (portWrongDir contra)
      typeCheck type value | (PortTyDesc x dir) | (PortTy y z) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (portWrongType prfWhyNot)
    typeCheck type value | (PortTyDesc x dir) | NatTy
      = No (WrongType type value) (portNoTypeN)
    typeCheck type value | (PortTyDesc x dir) | UnitTy
      = No (WrongType type value) (portNoTypeU)
    typeCheck type value | (PortTyDesc x dir) | BoolTy
      = No (WrongType type value) (portNoTypeB)
    typeCheck type value | (PortTyDesc x dir) | (FuncParamTy u a r)
      = No (WrongType type value) (portNoTypeFD)

  typeCheck type value | (NatTyDesc) with (value)
    typeCheck type value | (NatTyDesc) | (FuncTy param return)
      = No (WrongType type value) natNoTypeF
    typeCheck type value | (NatTyDesc) | ModuleTy
      = No (WrongType type value) natNoTypeM
    typeCheck type value | (NatTyDesc) | (ChanTy x)
      = No (WrongType type value) natNoTypeC
    typeCheck type value | (NatTyDesc) | (PortTy x dir)
      = No (WrongType type value) natNoTypeP
    typeCheck type value | (NatTyDesc) | (NatTy)
      = Yes ChkNat

    typeCheck type value | (NatTyDesc) | UnitTy
      = No (WrongType type value) natNoTypeU
    typeCheck type value | (NatTyDesc) | BoolTy
      = No (WrongType type value) natNoTypeB
    typeCheck type value | (NatTyDesc) | (FuncParamTy u a r)
      = No (WrongType type value) natNoTypeFD

  typeCheck type value | UnitTyDesc with (value)
    typeCheck type value | UnitTyDesc | (FuncTy x y)
      = No (WrongType type value) (unitNoTypeF)
    typeCheck type value | UnitTyDesc | ModuleTy
      = No (WrongType type value) (unitNoTypeM)
    typeCheck type value | UnitTyDesc | (ChanTy x)
      = No (WrongType type value) (unitNoTypeC)
    typeCheck type value | UnitTyDesc | (PortTy x dir)
      = No (WrongType type value) (unitNoTypePo)
    typeCheck type value | UnitTyDesc | NatTy
      = No (WrongType type value) (unitNoTypeN)
    typeCheck type value | UnitTyDesc | UnitTy
      = Yes ChkUnit
    typeCheck type value | UnitTyDesc | BoolTy
      = No (WrongType type value) unitNoTypeB

    typeCheck type value | UnitTyDesc | (FuncParamTy u a r)
      = No (WrongType type value) unitNoTypeFD

  typeCheck type value | (FuncParamTy u x y) with (value)
    typeCheck type value | (FuncParamTy u x y) | (FuncTy a r)
      = No (WrongType type value) (funcDefNoTypeF)

    typeCheck type value | (FuncParamTy u x y) | ModuleTy
      = No (WrongType type value) (funcDefNoTypeM)
    typeCheck type value | (FuncParamTy u x y) | (ChanTy z)
      = No (WrongType type value) (funcDefNoTypeC)
    typeCheck type value | (FuncParamTy u x y) | (PortTy z dir)
      = No (WrongType type value) (funcDefNoTypePo)
    typeCheck type value | (FuncParamTy u x y) | NatTy
      = No (WrongType type value) (funcDefNoTypeN)
    typeCheck type value | (FuncParamTy u x y) | UnitTy
      = No (WrongType type value) (funcDefNoTypeU)
    typeCheck type value | (FuncParamTy u x y) | (FuncParamTy i z w)
      = No (WrongType type value) funcParam

    typeCheck type value | (FuncParamTy u x y) | BoolTy
      = No (WrongType type value) (funcDefNoTypeB)


  typeCheck type value | BoolTyDesc with (value)
    typeCheck type value | BoolTyDesc | (FuncTy param return)
      = No (WrongType type value) boolNoTypeF
    typeCheck type value | BoolTyDesc | (FuncParamTy u param return)
      = No (WrongType type value) boolNoTypeFD
    typeCheck type value | BoolTyDesc | ModuleTy
      = No (WrongType type value) boolNoTypeM
    typeCheck type value | BoolTyDesc | (ChanTy x)
      = No (WrongType type value) boolNoTypeC
    typeCheck type value | BoolTyDesc | (PortTy x dir)
      = No (WrongType type value) boolNoTypePo
    typeCheck type value | BoolTyDesc | UnitTy
      = No (WrongType type value) boolNoTypeU
    typeCheck type value | BoolTyDesc | (NatTy)
      = No (WrongType type value) boolNoTypeN

    typeCheck type value | BoolTyDesc | BoolTy
      = Yes ChkBool


public export
data CheckedNat : (TyCheck type value) -> Type where
  IsCheckedNat : CheckedNat (ChkNat)

isBool : CheckedNat ChkBool -> Void
isBool IsCheckedNat impossible

isC : CheckedNat (ChkChan x) -> Void
isC IsCheckedNat impossible

isModule : CheckedNat ChkModule -> Void
isModule IsCheckedNat impossible

isP : CheckedNat (ChkPort x prf) -> Void
isP IsCheckedNat impossible

isUnit : CheckedNat ChkUnit -> Void
isUnit IsCheckedNat impossible

export
isCheckedNat : (prf : TyCheck type value) -> Dec (CheckedNat prf)
isCheckedNat (ChkNat) = Yes IsCheckedNat

isCheckedNat ChkModule = No isModule
isCheckedNat ChkUnit = No isUnit

isCheckedNat ChkBool = No isBool
isCheckedNat (ChkChan x) = No isC
isCheckedNat (ChkPort x prf) = No isP
-- [ EOF ]
