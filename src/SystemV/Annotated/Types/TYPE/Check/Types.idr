module SystemV.Annotated.Types.TYPE.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Annotated.Types.TYPE
import SystemV.Annotated.Types.TYPE.Equality


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

    ChkChan : (Equals Universe TYPE typeA typeB)
           -> (Equal senseA  senseB)
           -> (Equal intentA intentB)
           -> TyCheck (ChanTyDesc typeA senseA intentA) (ChanTy typeB senseB intentB)

    ChkPort : (Equals Universe TYPE typeA typeB)
           -> (Equal dirA dirB)
           -> (Equal senseA  senseB)
           -> (Equal intentA intentB)
           -> TyCheck (PortTyDesc typeA dirA senseA intentA) (PortTy typeB dirB senseB intentB)

public export
data Error = WrongType (TYPE (IDX TYPE)) (TYPE (IDX TERM))

funcNoTypeM  : TyCheck (FuncTy x y) ModuleTy -> Void
funcNoTypeM ChkModule impossible

funcNoTypeC  : TyCheck (FuncTy x y) (ChanTy z s i) -> Void
funcNoTypeC ChkModule impossible

funcNoTypePo : TyCheck (FuncTy x y) (PortTy z dir s i) -> Void
funcNoTypePo ChkModule impossible

funcNoTypeU  : TyCheck (FuncTy x y) UnitTy -> Void
funcNoTypeU ChkModule impossible

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

modeNoTypeC : TyCheck ModuleTyDesc (ChanTy ty s i) -> Void
modeNoTypeC ChkModule impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortTy ty dir s i) -> Void
modeNoTypePo ChkModule impossible

modeNoTypeU : TyCheck ModuleTyDesc UnitTy -> Void
modeNoTypeU ChkModule impossible

chanNotypeF : TyCheck (ChanTyDesc type s i) (FuncTy x y) -> Void
chanNotypeF ChkModule impossible

chanNotypeM  : TyCheck (ChanTyDesc type s i) ModuleTy -> Void
chanNotypeM ChkModule impossible

chanNotypePo : TyCheck (ChanTyDesc type s i) (PortTy ty dir sp ip) -> Void
chanNotypePo ChkModule impossible

chanNotypeU  : TyCheck (ChanTyDesc type s i) UnitTy -> Void
chanNotypeU ChkModule impossible

chanHasWrongType : (contra : Equals Universe TYPE x y -> Void)
                -> (prf    : TyCheck (ChanTyDesc x st it) (ChanTy y sv iv))
                          -> Void
chanHasWrongType contra (ChkChan x _ _) = contra x

chanHasWrongSens : (s = sv -> Void) -> TyCheck (ChanTyDesc x s i) (ChanTy tv sv iv) -> Void
chanHasWrongSens f (ChkChan _ prf _) = f prf

chanHasWrongIntent : (i = iv -> Void) -> TyCheck (ChanTyDesc x s i) (ChanTy tv sv iv) -> Void
chanHasWrongIntent f (ChkChan _ _ prf1) = f prf1

portNoTypeF : TyCheck (PortTyDesc type dir s i) (FuncTy x y) -> Void
portNoTypeF ChkModule impossible

portNoTypeM : TyCheck (PortTyDesc type dir s i) ModuleTy -> Void
portNoTypeM ChkModule impossible

portNoTypeC : TyCheck (PortTyDesc type dir s i) (ChanTy ty sc ic) -> Void
portNoTypeC ChkModule impossible

portNoTypeU : TyCheck (PortTyDesc type dir s i) UnitTy -> Void
portNoTypeU ChkModule impossible

portWrongType : (contra : Equals Universe TYPE ty val -> Void)
             -> (prf    : TyCheck (PortTyDesc ty dirT sa ia) (PortTy val dirV sb ib))
                       -> Void
portWrongType contra (ChkPort x _ _ _) = contra x

portWrongDir : (contra : dirT === dirV -> Void)
            -> (prf    : TyCheck (PortTyDesc ty dirT sa ia) (PortTy val dirV sb ib))
                      -> Void
portWrongDir contra (ChkPort _ prf _ _) = contra prf

portWrongSense : (s = sv -> Void) -> TyCheck (PortTyDesc x dir s i) (PortTy tv dv sv iv) -> Void
portWrongSense f (ChkPort _ _ prf1 _) = f prf1

portWrongIntent : (i = iv -> Void) -> TyCheck (PortTyDesc x dir s i) (PortTy tv dv sv iv) -> Void
portWrongIntent f (ChkPort _ _ _ prf2) = f prf2

unitNoTypeF : TyCheck UnitTyDesc (FuncTy x y) -> Void
unitNoTypeF ChkModule impossible

unitNoTypeM : TyCheck UnitTyDesc ModuleTy -> Void
unitNoTypeM ChkModule impossible

unitNoTypeC : TyCheck UnitTyDesc (ChanTy t s i) -> Void
unitNoTypeC ChkModule impossible

unitNoTypePo : TyCheck UnitTyDesc (PortTy x dir s i) -> Void
unitNoTypePo ChkModule impossible

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
    typeCheck type value | (FuncTy x y) | (ChanTy z s i)
      = No (WrongType type value) (funcNoTypeC)
    typeCheck type value | (FuncTy x y) | (PortTy z d s i)
      = No (WrongType type value) (funcNoTypePo)
    typeCheck type value | (FuncTy x y) | UnitTy
      = No (WrongType type value) (funcNoTypeU)

  typeCheck type value | ModuleTyDesc with (value)
    typeCheck type value | ModuleTyDesc | (FuncTy x y)
      = No (WrongType type value) (modeNoTypeF)
    typeCheck type value | ModuleTyDesc | ModuleTy
      = Yes ChkModule
    typeCheck type value | ModuleTyDesc | (ChanTy t s i)
      = No (WrongType type value) (modeNoTypeC)
    typeCheck type value | ModuleTyDesc | (PortTy x dir s i)
      = No (WrongType type value) (modeNoTypePo)
    typeCheck type value | ModuleTyDesc | UnitTy
      = No (WrongType type value) (modeNoTypeU)

  typeCheck type value | (ChanTyDesc x s i) with (value)
    typeCheck type value | (ChanTyDesc x s i) | (FuncTy y z)
      = No (WrongType type value) (chanNotypeF)
    typeCheck type value | (ChanTyDesc x s i) | ModuleTy
      = No (WrongType type value) (chanNotypeM)

    typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) with (DataTypes.decEq x tv)
      typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) | (Yes prfWhy) with (decEq s sv)
        typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) | (Yes prfWhy) | (Yes prfS) with (decEq i iv)
          typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) | (Yes prfWhy) | (Yes prfS) | (Yes prfI)
            = Yes (ChkChan prfWhy prfS prfI)

          typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) | (Yes prfWhy) | (Yes prfS) | (No contra)
            = No (WrongType type value) (chanHasWrongIntent contra)

        typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) | (Yes prfWhy) | (No contra)
          = No (WrongType type value) (chanHasWrongSens contra)

      typeCheck type value | (ChanTyDesc x s i) | (ChanTy tv sv iv) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (chanHasWrongType prfWhyNot)

    typeCheck type value | (ChanTyDesc x s i) | (PortTy y dir sp ip)
      = No (WrongType type value) (chanNotypePo)
    typeCheck type value | (ChanTyDesc x s i) | UnitTy
      = No (WrongType type value) (chanNotypeU)

  typeCheck type value | (PortTyDesc x dir s i) with (value)
    typeCheck type value | (PortTyDesc x dir s i) | (FuncTy y z)
      = No (WrongType type value) (portNoTypeF)
    typeCheck type value | (PortTyDesc x dir s i) | ModuleTy
      = No (WrongType type value) (portNoTypeM)
    typeCheck type value | (PortTyDesc x dir s i) | (ChanTy y sv iv)
      = No (WrongType type value) (portNoTypeC)
    typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  with (DataTypes.decEq x tv)
      typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) with (Direction.decEq dir dv)
        typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) | (Yes prfDir) with (decEq s sv)
          typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) | (Yes prfDir) | (Yes prfSense) with (decEq i iv)
            typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) | (Yes prfDir) | (Yes prfSense) | (Yes prfIntent)
              = Yes (ChkPort prfTypes prfDir prfSense prfIntent)
            typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) | (Yes prfDir) | (Yes prfSense) | (No contra)
              = No (WrongType type value) (portWrongIntent contra)
          typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) | (Yes prfDir) | (No contra)
            = No (WrongType type value) (portWrongSense contra)
        typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (Yes prfTypes) | (No contra)
          = No (WrongType type value) (portWrongDir contra)

      typeCheck type value | (PortTyDesc x dir s i) | (PortTy tv dv sv iv)  | (No msgWhyNot prfWhyNot)
        = No (WrongType type value) (portWrongType prfWhyNot)

    typeCheck type value | (PortTyDesc x dir s i) | UnitTy
      = No (WrongType type value) (portNoTypeU)

  typeCheck type value | UnitTyDesc with (value)
    typeCheck type value | UnitTyDesc | (FuncTy x y)
      = No (WrongType type value) (unitNoTypeF)
    typeCheck type value | UnitTyDesc | ModuleTy
      = No (WrongType type value) (unitNoTypeM)
    typeCheck type value | UnitTyDesc | (ChanTy x s i)
      = No (WrongType type value) (unitNoTypeC)
    typeCheck type value | UnitTyDesc | (PortTy x dir s i)
      = No (WrongType type value) (unitNoTypePo)
    typeCheck type value | UnitTyDesc | UnitTy
      = Yes ChkUnit


-- [ EOF ]
