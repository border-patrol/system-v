module SystemV.Types.TYPE.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Utilities

import SystemV.Types.Direction
import SystemV.Types.TYPE
import SystemV.Types.TYPE.Equality


%default total

||| A predicate to type check types against type formers.
public export
data TyCheck : (type  : TYPE (IDX TYPE))
            -> (value : TYPE (IDX TERM))
            -> Type
  where
    ChkModule : TyCheck ModuleTyDesc  ModuleTy
    ChkUnit   : TyCheck UnitTyDesc    UnitTy

    ChkNat    : (prf : n === m)
                    -> TyCheck (NatTyDesc n) (NatTy m)

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
funcNoTypeM (ChkNat prf) impossible
funcNoTypeM (ChkFunc z w) impossible
funcNoTypeM (ChkChan z) impossible
funcNoTypeM (ChkPort z prf) impossible

funcNoTypeC  : TyCheck (FuncTy x y) (ChanTy z) -> Void
funcNoTypeC ChkModule impossible
funcNoTypeC ChkUnit impossible
funcNoTypeC (ChkNat prf) impossible
funcNoTypeC (ChkFunc w v) impossible
funcNoTypeC (ChkChan w) impossible
funcNoTypeC (ChkPort w prf) impossible

funcNoTypePo : TyCheck (FuncTy x y) (PortTy z dir) -> Void
funcNoTypePo ChkModule impossible
funcNoTypePo ChkUnit impossible
funcNoTypePo (ChkNat prf) impossible
funcNoTypePo (ChkFunc w v) impossible
funcNoTypePo (ChkChan w) impossible
funcNoTypePo (ChkPort w prf) impossible

funcNoTypeN : TyCheck (FuncTy x y) (NatTy n) -> Void
funcNoTypeN ChkModule impossible
funcNoTypeN ChkUnit impossible
funcNoTypeN (ChkNat prf) impossible
funcNoTypeN (ChkFunc z w) impossible
funcNoTypeN (ChkChan z) impossible
funcNoTypeN (ChkPort z prf) impossible

funcNoTypeU  : TyCheck (FuncTy x y) UnitTy -> Void
funcNoTypeU ChkModule impossible
funcNoTypeU ChkUnit impossible
funcNoTypeU (ChkNat prf) impossible
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
modeNoTypeF (ChkNat prf) impossible
modeNoTypeF (ChkFunc z w) impossible
modeNoTypeF (ChkChan z) impossible
modeNoTypeF (ChkPort z prf) impossible

modeNoTypeC : TyCheck ModuleTyDesc (ChanTy ty) -> Void
modeNoTypeC ChkModule impossible
modeNoTypeC ChkUnit impossible
modeNoTypeC (ChkNat prf) impossible
modeNoTypeC (ChkFunc x y) impossible
modeNoTypeC (ChkChan x) impossible
modeNoTypeC (ChkPort x prf) impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortTy ty dir) -> Void
modeNoTypePo ChkModule impossible
modeNoTypePo ChkUnit impossible
modeNoTypePo (ChkNat prf) impossible
modeNoTypePo (ChkFunc x y) impossible
modeNoTypePo (ChkChan x) impossible
modeNoTypePo (ChkPort x prf) impossible

modeNoTypeN : TyCheck ModuleTyDesc (NatTy n) -> Void
modeNoTypeN ChkModule impossible
modeNoTypeN ChkUnit impossible
modeNoTypeN (ChkNat prf) impossible
modeNoTypeN (ChkFunc x y) impossible
modeNoTypeN (ChkChan x) impossible
modeNoTypeN (ChkPort x prf) impossible

modeNoTypeU : TyCheck ModuleTyDesc UnitTy -> Void
modeNoTypeU ChkModule impossible
modeNoTypeU ChkUnit impossible
modeNoTypeU (ChkNat prf) impossible
modeNoTypeU (ChkFunc x y) impossible
modeNoTypeU (ChkChan x) impossible
modeNoTypeU (ChkPort x prf) impossible

chanNotypeF : TyCheck (ChanTyDesc type) (FuncTy x y) -> Void
chanNotypeF ChkModule impossible
chanNotypeF ChkUnit impossible
chanNotypeF (ChkNat prf) impossible
chanNotypeF (ChkFunc z w) impossible
chanNotypeF (ChkChan z) impossible
chanNotypeF (ChkPort z prf) impossible

chanNotypeM  : TyCheck (ChanTyDesc type) ModuleTy -> Void
chanNotypeM ChkModule impossible
chanNotypeM ChkUnit impossible
chanNotypeM (ChkNat prf) impossible
chanNotypeM (ChkFunc x y) impossible
chanNotypeM (ChkChan x) impossible
chanNotypeM (ChkPort x prf) impossible

chanNotypePo : TyCheck (ChanTyDesc type) (PortTy ty dir) -> Void
chanNotypePo ChkModule impossible
chanNotypePo ChkUnit impossible
chanNotypePo (ChkNat prf) impossible
chanNotypePo (ChkFunc x y) impossible
chanNotypePo (ChkChan x) impossible
chanNotypePo (ChkPort x prf) impossible

chanNotypeN : TyCheck (ChanTyDesc x) (NatTy n) -> Void
chanNotypeN ChkModule impossible
chanNotypeN ChkUnit impossible
chanNotypeN (ChkNat prf) impossible
chanNotypeN (ChkFunc y z) impossible
chanNotypeN (ChkChan y) impossible
chanNotypeN (ChkPort y prf) impossible

chanNotypeU  : TyCheck (ChanTyDesc type) UnitTy -> Void
chanNotypeU ChkModule impossible
chanNotypeU ChkUnit impossible
chanNotypeU (ChkNat prf) impossible
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
portNoTypeF (ChkNat prf) impossible
portNoTypeF (ChkFunc z w) impossible
portNoTypeF (ChkChan z) impossible
portNoTypeF (ChkPort z prf) impossible

portNoTypeM : TyCheck (PortTyDesc type dir) ModuleTy -> Void
portNoTypeM ChkModule impossible
portNoTypeM ChkUnit impossible
portNoTypeM (ChkNat prf) impossible
portNoTypeM (ChkFunc x y) impossible
portNoTypeM (ChkChan x) impossible
portNoTypeM (ChkPort x prf) impossible

portNoTypeC : TyCheck (PortTyDesc type dir) (ChanTy ty) -> Void
portNoTypeC ChkModule impossible
portNoTypeC ChkUnit impossible
portNoTypeC (ChkNat prf) impossible
portNoTypeC (ChkFunc x y) impossible
portNoTypeC (ChkChan x) impossible
portNoTypeC (ChkPort x prf) impossible

portNoTypeN : TyCheck (PortTyDesc x dir) (NatTy n) -> Void
portNoTypeN ChkModule impossible
portNoTypeN ChkUnit impossible
portNoTypeN (ChkNat prf) impossible
portNoTypeN (ChkFunc y z) impossible
portNoTypeN (ChkChan y) impossible
portNoTypeN (ChkPort y prf) impossible

portNoTypeU : TyCheck (PortTyDesc type dir) UnitTy -> Void
portNoTypeU ChkModule impossible
portNoTypeU ChkUnit impossible
portNoTypeU (ChkNat prf) impossible
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

natNoTypeF : TyCheck (NatTyDesc n) (FuncTy param return) -> Void
natNoTypeF ChkModule impossible
natNoTypeF ChkUnit impossible
natNoTypeF (ChkNat prf) impossible
natNoTypeF (ChkFunc x y) impossible
natNoTypeF (ChkChan x) impossible
natNoTypeF (ChkPort x prf) impossible


natNoTypeC : TyCheck (NatTyDesc n) (ChanTy x) -> Void
natNoTypeC ChkModule impossible
natNoTypeC ChkUnit impossible
natNoTypeC (ChkNat prf) impossible
natNoTypeC (ChkFunc y z) impossible
natNoTypeC (ChkChan y) impossible
natNoTypeC (ChkPort y prf) impossible

natNoTypeM : TyCheck (NatTyDesc n) ModuleTy -> Void
natNoTypeM ChkModule impossible
natNoTypeM ChkUnit impossible
natNoTypeM (ChkNat prf) impossible
natNoTypeM (ChkFunc x y) impossible
natNoTypeM (ChkChan x) impossible
natNoTypeM (ChkPort x prf) impossible

natNoTypeP : TyCheck (NatTyDesc n) (PortTy x dir) -> Void
natNoTypeP ChkModule impossible
natNoTypeP ChkUnit impossible
natNoTypeP (ChkNat prf) impossible
natNoTypeP (ChkFunc y z) impossible
natNoTypeP (ChkChan y) impossible
natNoTypeP (ChkPort y prf) impossible

natNoTypeU : TyCheck (NatTyDesc n) UnitTy -> Void
natNoTypeU ChkModule impossible
natNoTypeU ChkUnit impossible
natNoTypeU (ChkNat prf) impossible
natNoTypeU (ChkFunc x y) impossible
natNoTypeU (ChkChan x) impossible
natNoTypeU (ChkPort x prf) impossible

natNoWrongNat : (n = m -> Void) -> TyCheck (NatTyDesc n) (NatTy m) -> Void
natNoWrongNat f (ChkNat Refl) = f Refl

unitNoTypeF : TyCheck UnitTyDesc (FuncTy x y) -> Void
unitNoTypeF ChkModule impossible
unitNoTypeF ChkUnit impossible
unitNoTypeF (ChkNat prf) impossible
unitNoTypeF (ChkFunc z w) impossible
unitNoTypeF (ChkChan z) impossible
unitNoTypeF (ChkPort z prf) impossible

unitNoTypeM : TyCheck UnitTyDesc ModuleTy -> Void
unitNoTypeM ChkModule impossible
unitNoTypeM ChkUnit impossible
unitNoTypeM (ChkNat prf) impossible
unitNoTypeM (ChkFunc x y) impossible
unitNoTypeM (ChkChan x) impossible
unitNoTypeM (ChkPort x prf) impossible

unitNoTypeC : TyCheck UnitTyDesc (ChanTy t) -> Void
unitNoTypeC ChkModule impossible
unitNoTypeC ChkUnit impossible
unitNoTypeC (ChkNat prf) impossible
unitNoTypeC (ChkFunc x y) impossible
unitNoTypeC (ChkChan x) impossible
unitNoTypeC (ChkPort x prf) impossible

unitNoTypePo : TyCheck UnitTyDesc (PortTy x dir) -> Void
unitNoTypePo ChkModule impossible
unitNoTypePo ChkUnit impossible
unitNoTypePo (ChkNat prf) impossible
unitNoTypePo (ChkFunc y z) impossible
unitNoTypePo (ChkChan y) impossible
unitNoTypePo (ChkPort y prf) impossible

unitNoTypeN : TyCheck UnitTyDesc (NatTy n) -> Void
unitNoTypeN ChkModule impossible
unitNoTypeN ChkUnit impossible
unitNoTypeN (ChkNat prf) impossible
unitNoTypeN (ChkFunc x y) impossible
unitNoTypeN (ChkChan x) impossible
unitNoTypeN (ChkPort x prf) impossible

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
    typeCheck type value | (FuncTy x y) | (NatTy n)
      = No (WrongType type value) (funcNoTypeN)
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
    typeCheck type value | ModuleTyDesc | (NatTy n)
      = No (WrongType type value) (modeNoTypeN)
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
    typeCheck type value | (ChanTyDesc x) | (NatTy n)
      = No (WrongType type value) (chanNotypeN)
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
    typeCheck type value | (PortTyDesc x dir) | (NatTy n)
      = No (WrongType type value) (portNoTypeN)
    typeCheck type value | (PortTyDesc x dir) | UnitTy
      = No (WrongType type value) (portNoTypeU)

  typeCheck type value | (NatTyDesc n) with (value)
    typeCheck type value | (NatTyDesc n) | (FuncTy param return)
      = No (WrongType type value) natNoTypeF
    typeCheck type value | (NatTyDesc n) | ModuleTy
      = No (WrongType type value) natNoTypeM
    typeCheck type value | (NatTyDesc n) | (ChanTy x)
      = No (WrongType type value) natNoTypeC
    typeCheck type value | (NatTyDesc n) | (PortTy x dir)
      = No (WrongType type value) natNoTypeP
    typeCheck type value | (NatTyDesc n) | (NatTy m) with (decEq n m)
      typeCheck type value | (NatTyDesc m) | (NatTy m) | (Yes Refl)
        = Yes (ChkNat Refl)
      typeCheck type value | (NatTyDesc n) | (NatTy m) | (No contra)
        = No (WrongType type value) (natNoWrongNat contra)

    typeCheck type value | (NatTyDesc n) | UnitTy
      = No (WrongType type value) natNoTypeU

  typeCheck type value | UnitTyDesc with (value)
    typeCheck type value | UnitTyDesc | (FuncTy x y)
      = No (WrongType type value) (unitNoTypeF)
    typeCheck type value | UnitTyDesc | ModuleTy
      = No (WrongType type value) (unitNoTypeM)
    typeCheck type value | UnitTyDesc | (ChanTy x)
      = No (WrongType type value) (unitNoTypeC)
    typeCheck type value | UnitTyDesc | (PortTy x dir)
      = No (WrongType type value) (unitNoTypePo)
    typeCheck type value | UnitTyDesc | (NatTy n)
      = No (WrongType type value) (unitNoTypeN)
    typeCheck type value | UnitTyDesc | UnitTy
      = Yes ChkUnit
