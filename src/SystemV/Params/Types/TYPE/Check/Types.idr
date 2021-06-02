module SystemV.Params.Types.TYPE.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality

import SystemV.Params.Types.TYPE.Equality.DataTerms

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

    ChkChan  : TyCheck ChanTyDesc ChanTy

    ChkPort : (dirA === dirB)
           -> TyCheck (PortTyDesc dirA) (PortTy dirB)

public export
data Error = WrongType (TYPE (IDX TYPE)) (TYPE (IDX TERM))

-- ## Function Voids

funcNoTypeM  : TyCheck (FuncTy x y) ModuleTy -> Void
funcNoTypeM ChkModule impossible

funcNoTypeC  : TyCheck (FuncTy x y) ChanTy -> Void
funcNoTypeC ChkModule impossible


funcNoTypePo : TyCheck (FuncTy x y) (PortTy dir) -> Void
funcNoTypePo ChkModule impossible

funcNoTypeN : TyCheck (FuncTy x y) (NatTy) -> Void
funcNoTypeN ChkModule impossible


funcNoTypeU  : TyCheck (FuncTy x y) UnitTy -> Void
funcNoTypeU ChkModule impossible


funcNoTypeB  : TyCheck (FuncTy x y) BoolTy -> Void
funcNoTypeB ChkModule impossible

funcNoTypeFD : TyCheck (FuncTy x y) (FuncParamTy u a r) -> Void
funcNoTypeFD ChkModule impossible

-- ## Function Defaults Voids

funcDefNoTypeM  : TyCheck (FuncParamTy u x y) ModuleTy -> Void
funcDefNoTypeM ChkModule impossible


funcDefNoTypeC  : TyCheck (FuncParamTy u x y) ChanTy -> Void
funcDefNoTypeC ChkModule impossible


funcDefNoTypePo : TyCheck (FuncParamTy u x y) (PortTy dir) -> Void
funcDefNoTypePo ChkModule impossible


funcDefNoTypeN : TyCheck (FuncParamTy u x y) (NatTy) -> Void
funcDefNoTypeN ChkModule impossible

funcDefNoTypeU  : TyCheck (FuncParamTy u x y) UnitTy -> Void
funcDefNoTypeU ChkModule impossible


funcDefNoTypeB  : TyCheck (FuncParamTy u x y) BoolTy -> Void
funcDefNoTypeB ChkModule impossible

funcDefNoTypeF : TyCheck (FuncParamTy u x y) (FuncTy a r) -> Void
funcDefNoTypeF ChkModule impossible

-- ## Modules

modeNoTypeF : TyCheck ModuleTyDesc (FuncTy x y) -> Void
modeNoTypeF ChkModule impossible

modeNoTypeFD : TyCheck ModuleTyDesc (FuncParamTy u x y) -> Void
modeNoTypeFD ChkModule impossible

modeNoTypeC : TyCheck ModuleTyDesc ChanTy -> Void
modeNoTypeC ChkModule impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortTy dir) -> Void
modeNoTypePo ChkModule impossible

modeNoTypeN : TyCheck ModuleTyDesc (NatTy) -> Void
modeNoTypeN ChkModule impossible


modeNoTypeU : TyCheck ModuleTyDesc UnitTy -> Void
modeNoTypeU ChkModule impossible


modeNoTypeB : TyCheck ModuleTyDesc BoolTy -> Void
modeNoTypeB ChkModule impossible


-- ## Channels

chanNotypeF : TyCheck ChanTyDesc (FuncTy x y) -> Void
chanNotypeF ChkModule impossible


chanNotypeFD : TyCheck ChanTyDesc (FuncParamTy u x y) -> Void
chanNotypeFD ChkModule impossible

chanNotypeM  : TyCheck ChanTyDesc ModuleTy -> Void
chanNotypeM ChkModule impossible

chanNotypePo : TyCheck ChanTyDesc (PortTy dir) -> Void
chanNotypePo ChkModule impossible

chanNotypeN : TyCheck ChanTyDesc (NatTy) -> Void
chanNotypeN ChkModule impossible

chanNotypeU  : TyCheck ChanTyDesc UnitTy -> Void
chanNotypeU ChkModule impossible


chanNotypeB  : TyCheck ChanTyDesc BoolTy -> Void
chanNotypeB ChkModule impossible

-- ## Ports

portNoTypeF : TyCheck (PortTyDesc dir) (FuncTy x y) -> Void
portNoTypeF ChkModule impossible

portNoTypeFD : TyCheck (PortTyDesc dir) (FuncParamTy u x y) -> Void
portNoTypeFD ChkModule impossible

portNoTypeM : TyCheck (PortTyDesc dir) ModuleTy -> Void
portNoTypeM ChkModule impossible


portNoTypeC : TyCheck (PortTyDesc dir) ChanTy -> Void
portNoTypeC ChkModule impossible


portNoTypeN : TyCheck (PortTyDesc dir) NatTy -> Void
portNoTypeN ChkModule impossible


portNoTypeU : TyCheck (PortTyDesc dir) UnitTy -> Void
portNoTypeU ChkModule impossible


portNoTypeB : TyCheck (PortTyDesc dir) BoolTy -> Void
portNoTypeB ChkModule impossible

portWrongDir : (contra : dirT === dirV -> Void)
            -> (prf    : TyCheck (PortTyDesc dirT) (PortTy dirV))
                      -> Void
portWrongDir contra (ChkPort Refl) = contra Refl

-- ## Nats

natNoTypeF : TyCheck (NatTyDesc) (FuncTy param return) -> Void
natNoTypeF ChkModule impossible

natNoTypeFD : TyCheck (NatTyDesc) (FuncParamTy u param return) -> Void
natNoTypeFD ChkModule impossible


natNoTypeC : TyCheck (NatTyDesc) ChanTy -> Void
natNoTypeC ChkModule impossible


natNoTypeM : TyCheck (NatTyDesc) ModuleTy -> Void
natNoTypeM ChkModule impossible


natNoTypeP : TyCheck (NatTyDesc) (PortTy dir) -> Void
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


unitNoTypeC : TyCheck UnitTyDesc ChanTy -> Void
unitNoTypeC ChkModule impossible

unitNoTypePo : TyCheck UnitTyDesc (PortTy dir) -> Void
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


boolNoTypeC : TyCheck BoolTyDesc ChanTy -> Void
boolNoTypeC ChkModule impossible

boolNoTypePo : TyCheck BoolTyDesc (PortTy dir) -> Void
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
    typeCheck type value | (FuncTy x y) | ChanTy
      = No (WrongType type value) (funcNoTypeC)
    typeCheck type value | (FuncTy x y) | (PortTy dir)
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
    typeCheck type value | ModuleTyDesc | ChanTy
      = No (WrongType type value) (modeNoTypeC)
    typeCheck type value | ModuleTyDesc | (PortTy dir)
      = No (WrongType type value) (modeNoTypePo)
    typeCheck type value | ModuleTyDesc | NatTy
      = No (WrongType type value) (modeNoTypeN)
    typeCheck type value | ModuleTyDesc | UnitTy
      = No (WrongType type value) (modeNoTypeU)
    typeCheck type value | ModuleTyDesc | BoolTy
      = No (WrongType type value) (modeNoTypeB)
    typeCheck type value | ModuleTyDesc | (FuncParamTy u a r)
      = No (WrongType type value) (modeNoTypeFD)

  typeCheck type value | ChanTyDesc with (value)
    typeCheck type value | ChanTyDesc | (FuncTy y z)
      = No (WrongType type value) (chanNotypeF)
    typeCheck type value | ChanTyDesc | ModuleTy
      = No (WrongType type value) (chanNotypeM)

    typeCheck type value | ChanTyDesc | ChanTy
      = Yes ChkChan

    typeCheck type value | ChanTyDesc | (PortTy dir)
      = No (WrongType type value) (chanNotypePo)
    typeCheck type value | ChanTyDesc | NatTy
      = No (WrongType type value) (chanNotypeN)
    typeCheck type value | ChanTyDesc | UnitTy
      = No (WrongType type value) (chanNotypeU)
    typeCheck type value | ChanTyDesc | BoolTy
      = No (WrongType type value) (chanNotypeB)
    typeCheck type value | ChanTyDesc | (FuncParamTy u a r)
      = No (WrongType type value) (chanNotypeFD)

  typeCheck type value | (PortTyDesc dir) with (value)
    typeCheck type value | (PortTyDesc dir) | (FuncTy y z)
      = No (WrongType type value) (portNoTypeF)
    typeCheck type value | (PortTyDesc dir) | ModuleTy
      = No (WrongType type value) (portNoTypeM)
    typeCheck type value | (PortTyDesc dir) | ChanTy
      = No (WrongType type value) (portNoTypeC)
    typeCheck type value | (PortTyDesc dir) | (PortTy z) with (Direction.decEq dir z)
        typeCheck type value | (PortTyDesc dir) | (PortTy dir) | (Yes Refl)
          = Yes (ChkPort Refl)
        typeCheck type value | (PortTyDesc dir) | (PortTy z) | (No contra)
          = No (WrongType type value) (portWrongDir contra)

    typeCheck type value | (PortTyDesc dir) | NatTy
      = No (WrongType type value) (portNoTypeN)
    typeCheck type value | (PortTyDesc dir) | UnitTy
      = No (WrongType type value) (portNoTypeU)
    typeCheck type value | (PortTyDesc dir) | BoolTy
      = No (WrongType type value) (portNoTypeB)
    typeCheck type value | (PortTyDesc dir) | (FuncParamTy u a r)
      = No (WrongType type value) (portNoTypeFD)

  typeCheck type value | (NatTyDesc) with (value)
    typeCheck type value | (NatTyDesc) | (FuncTy param return)
      = No (WrongType type value) natNoTypeF
    typeCheck type value | (NatTyDesc) | ModuleTy
      = No (WrongType type value) natNoTypeM
    typeCheck type value | (NatTyDesc) | ChanTy
      = No (WrongType type value) natNoTypeC
    typeCheck type value | (NatTyDesc) | (PortTy dir)
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
    typeCheck type value | UnitTyDesc | ChanTy
      = No (WrongType type value) (unitNoTypeC)
    typeCheck type value | UnitTyDesc | (PortTy dir)
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
    typeCheck type value | (FuncParamTy u x y) | ChanTy
      = No (WrongType type value) (funcDefNoTypeC)
    typeCheck type value | (FuncParamTy u x y) | (PortTy dir)
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
    typeCheck type value | BoolTyDesc | ChanTy
      = No (WrongType type value) boolNoTypeC
    typeCheck type value | BoolTyDesc | (PortTy dir)
      = No (WrongType type value) boolNoTypePo
    typeCheck type value | BoolTyDesc | UnitTy
      = No (WrongType type value) boolNoTypeU
    typeCheck type value | BoolTyDesc | (NatTy)
      = No (WrongType type value) boolNoTypeN

    typeCheck type value | BoolTyDesc | BoolTy
      = Yes ChkBool


public export
data CheckedNat : (TyCheck type value) -> Type where
  IsCheckedNat : CheckedNat ChkNat

isBool : CheckedNat ChkBool -> Void
isBool IsCheckedNat impossible

isC : CheckedNat ChkChan -> Void
isC IsCheckedNat impossible

isModule : CheckedNat ChkModule -> Void
isModule IsCheckedNat impossible

isP : CheckedNat (ChkPort prf) -> Void
isP IsCheckedNat impossible

isUnit : CheckedNat ChkUnit -> Void
isUnit IsCheckedNat impossible

export
isCheckedNat : (prf : TyCheck type value) -> Dec (CheckedNat prf)
isCheckedNat (ChkNat) = Yes IsCheckedNat

isCheckedNat ChkModule = No isModule
isCheckedNat ChkUnit = No isUnit

isCheckedNat ChkBool = No isBool
isCheckedNat ChkChan = No isC
isCheckedNat (ChkPort prf) = No isP
-- [ EOF ]
