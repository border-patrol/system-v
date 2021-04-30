module SystemV.Params.Types.TYPE.Check.Types

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality

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

    ChkBool : TyCheck BoolTyDesc BoolTy

    ChkFuncDef : TyCheck                       paramTy                                 paramValue
              -> TyCheck                               returnTy                                   returnValue
              -> TyCheck (FuncDefTy (IDX TYPE) paramTy returnTy) (FuncDefTy (IDX TERM) paramValue returnValue)

    ChkFuncDefD : (paramTy : TYPE (DATA TYPE))
               -> TyCheck                               returnTy                                  returnValue
               -> TyCheck (FuncDefTy (DATA TYPE) paramTy returnTy) (FuncDefTy (DATA TYPE) paramTy returnValue)

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

-- ## Function Voids

funcNoTypeM  : TyCheck (FuncTy x y) ModuleTy -> Void
funcNoTypeM ChkModule impossible
funcNoTypeM ChkUnit impossible
funcNoTypeM (ChkNat prf) impossible
funcNoTypeM ChkBool impossible
funcNoTypeM (ChkFuncDef z w) impossible
funcNoTypeM (ChkFuncDefD z w) impossible
funcNoTypeM (ChkFunc z w) impossible
funcNoTypeM (ChkChan z) impossible
funcNoTypeM (ChkPort z prf) impossible

funcNoTypeC  : TyCheck (FuncTy x y) (ChanTy z) -> Void
funcNoTypeC ChkModule impossible
funcNoTypeC ChkUnit impossible
funcNoTypeC (ChkNat prf) impossible
funcNoTypeC ChkBool impossible
funcNoTypeC (ChkFuncDef w v) impossible
funcNoTypeC (ChkFuncDefD w v) impossible
funcNoTypeC (ChkFunc w v) impossible
funcNoTypeC (ChkChan w) impossible
funcNoTypeC (ChkPort w prf) impossible

funcNoTypePo : TyCheck (FuncTy x y) (PortTy z dir) -> Void
funcNoTypePo ChkModule impossible
funcNoTypePo ChkUnit impossible
funcNoTypePo (ChkNat prf) impossible
funcNoTypePo ChkBool impossible
funcNoTypePo (ChkFuncDef w v) impossible
funcNoTypePo (ChkFuncDefD w v) impossible
funcNoTypePo (ChkFunc w v) impossible
funcNoTypePo (ChkChan w) impossible
funcNoTypePo (ChkPort w prf) impossible

funcNoTypeN : TyCheck (FuncTy x y) (NatTy n) -> Void
funcNoTypeN ChkModule impossible
funcNoTypeN ChkUnit impossible
funcNoTypeN (ChkNat prf) impossible
funcNoTypeN ChkBool impossible
funcNoTypeN (ChkFuncDef z w) impossible
funcNoTypeN (ChkFuncDefD z w) impossible
funcNoTypeN (ChkFunc z w) impossible
funcNoTypeN (ChkChan z) impossible
funcNoTypeN (ChkPort z prf) impossible

funcNoTypeU  : TyCheck (FuncTy x y) UnitTy -> Void
funcNoTypeU ChkModule impossible
funcNoTypeU ChkUnit impossible
funcNoTypeU (ChkNat prf) impossible
funcNoTypeU ChkBool impossible
funcNoTypeU (ChkFuncDef z w) impossible
funcNoTypeU (ChkFuncDefD z w) impossible
funcNoTypeU (ChkFunc z w) impossible
funcNoTypeU (ChkChan z) impossible
funcNoTypeU (ChkPort z prf) impossible

funcNoTypeB  : TyCheck (FuncTy x y) BoolTy -> Void
funcNoTypeB ChkModule impossible
funcNoTypeB ChkUnit impossible
funcNoTypeB (ChkNat prf) impossible
funcNoTypeB ChkBool impossible
funcNoTypeB (ChkFuncDef z w) impossible
funcNoTypeB (ChkFuncDefD z w) impossible
funcNoTypeB (ChkFunc z w) impossible
funcNoTypeB (ChkChan z) impossible
funcNoTypeB (ChkPort z prf) impossible

funcNoTyCheckParam : (contra : TyCheck ty val -> Void)
                  -> (prf    : TyCheck (FuncTy ty rty) (FuncTy val rval))
                            -> Void
funcNoTyCheckParam contra (ChkFunc x y) = contra x

funcNoTyCheckRet : (contra : TyCheck rty rval -> Void)
                -> (prf    : TyCheck (FuncTy ty rty) (FuncTy val rval))
                          -> Void
funcNoTyCheckRet contra (ChkFunc x y) = contra y

funcNoTypeFD : TyCheck (FuncTy x y) (FuncDefTy u a r) -> Void
funcNoTypeFD ChkModule impossible
funcNoTypeFD ChkUnit impossible
funcNoTypeFD (ChkNat prf) impossible
funcNoTypeFD ChkBool impossible
funcNoTypeFD (ChkFuncDef z w) impossible
funcNoTypeFD (ChkFuncDefD z w) impossible
funcNoTypeFD (ChkFunc z w) impossible
funcNoTypeFD (ChkChan z) impossible
funcNoTypeFD (ChkPort z prf) impossible

-- ## Function Defaults Voids

funcDefNoTypeM  : TyCheck (FuncDefTy u x y) ModuleTy -> Void
funcDefNoTypeM ChkModule impossible
funcDefNoTypeM ChkUnit impossible
funcDefNoTypeM (ChkNat prf) impossible
funcDefNoTypeM ChkBool impossible
funcDefNoTypeM (ChkFuncDef z w) impossible
funcDefNoTypeM (ChkFuncDefD z w) impossible
funcDefNoTypeM (ChkFunc z w) impossible
funcDefNoTypeM (ChkChan z) impossible
funcDefNoTypeM (ChkPort z prf) impossible

funcDefNoTypeC  : TyCheck (FuncDefTy u x y) (ChanTy z) -> Void
funcDefNoTypeC ChkModule impossible
funcDefNoTypeC ChkUnit impossible
funcDefNoTypeC (ChkNat prf) impossible
funcDefNoTypeC ChkBool impossible
funcDefNoTypeC (ChkFuncDef w v) impossible
funcDefNoTypeC (ChkFuncDefD w v) impossible
funcDefNoTypeC (ChkFunc w v) impossible
funcDefNoTypeC (ChkChan w) impossible
funcDefNoTypeC (ChkPort w prf) impossible

funcDefNoTypePo : TyCheck (FuncDefTy u x y) (PortTy z dir) -> Void
funcDefNoTypePo ChkModule impossible
funcDefNoTypePo ChkUnit impossible
funcDefNoTypePo (ChkNat prf) impossible
funcDefNoTypePo ChkBool impossible
funcDefNoTypePo (ChkFuncDef w v) impossible
funcDefNoTypePo (ChkFuncDefD w v) impossible
funcDefNoTypePo (ChkFunc w v) impossible
funcDefNoTypePo (ChkChan w) impossible
funcDefNoTypePo (ChkPort w prf) impossible

funcDefNoTypeN : TyCheck (FuncDefTy u x y) (NatTy n) -> Void
funcDefNoTypeN ChkModule impossible
funcDefNoTypeN ChkUnit impossible
funcDefNoTypeN (ChkNat prf) impossible
funcDefNoTypeN ChkBool impossible
funcDefNoTypeN (ChkFuncDef z w) impossible
funcDefNoTypeN (ChkFuncDefD z w) impossible
funcDefNoTypeN (ChkFunc z w) impossible
funcDefNoTypeN (ChkChan z) impossible
funcDefNoTypeN (ChkPort z prf) impossible

funcDefNoTypeU  : TyCheck (FuncDefTy u x y) UnitTy -> Void
funcDefNoTypeU ChkModule impossible
funcDefNoTypeU ChkUnit impossible
funcDefNoTypeU (ChkNat prf) impossible
funcDefNoTypeU ChkBool impossible
funcDefNoTypeU (ChkFuncDef z w) impossible
funcDefNoTypeU (ChkFuncDefD z w) impossible
funcDefNoTypeU (ChkFunc z w) impossible
funcDefNoTypeU (ChkChan z) impossible
funcDefNoTypeU (ChkPort z prf) impossible

funcDefNoTypeB  : TyCheck (FuncDefTy u x y) BoolTy -> Void
funcDefNoTypeB ChkModule impossible
funcDefNoTypeB ChkUnit impossible
funcDefNoTypeB (ChkNat prf) impossible
funcDefNoTypeB ChkBool impossible
funcDefNoTypeB (ChkFuncDef z w) impossible
funcDefNoTypeB (ChkFuncDefD z w) impossible
funcDefNoTypeB (ChkFunc z w) impossible
funcDefNoTypeB (ChkChan z) impossible
funcDefNoTypeB (ChkPort z prf) impossible

funcDefNoTyCheckParam : (contra : TyCheck ty val -> Void)
                     -> (prf    : TyCheck (FuncDefTy (IDX TYPE) ty rty) (FuncDefTy (IDX TERM) val rval))
                               -> Void
funcDefNoTyCheckParam contra (ChkFuncDef x y) = contra x

funcDefNoTyCheckRet : (contra : TyCheck rty rval -> Void)
                   -> (prf    : TyCheck (FuncDefTy u ty rty) (FuncDefTy v val rval))
                             -> Void
funcDefNoTyCheckRet contra (ChkFuncDef x y) = contra y
funcDefNoTyCheckRet contra (ChkFuncDefD x y) = contra y

funcDefNoTypeF : TyCheck (FuncDefTy u x y) (FuncTy a r) -> Void
funcDefNoTypeF ChkModule impossible
funcDefNoTypeF ChkUnit impossible
funcDefNoTypeF (ChkNat prf) impossible
funcDefNoTypeF ChkBool impossible
funcDefNoTypeF (ChkFuncDef z w) impossible
funcDefNoTypeF (ChkFuncDefD z w) impossible
funcDefNoTypeF (ChkFunc z w) impossible
funcDefNoTypeF (ChkChan z) impossible
funcDefNoTypeF (ChkPort z prf) impossible

-- ## Modules

modeNoTypeF : TyCheck ModuleTyDesc (FuncTy x y) -> Void
modeNoTypeF ChkModule impossible
modeNoTypeF ChkUnit impossible
modeNoTypeF (ChkNat prf) impossible
modeNoTypeF ChkBool impossible
modeNoTypeF (ChkFuncDef z w) impossible
modeNoTypeF (ChkFuncDefD z w) impossible
modeNoTypeF (ChkFunc z w) impossible
modeNoTypeF (ChkChan z) impossible
modeNoTypeF (ChkPort z prf) impossible

modeNoTypeFD : TyCheck ModuleTyDesc (FuncDefTy u x y) -> Void
modeNoTypeFD ChkModule impossible
modeNoTypeFD ChkUnit impossible
modeNoTypeFD (ChkNat prf) impossible
modeNoTypeFD ChkBool impossible
modeNoTypeFD (ChkFuncDef z w) impossible
modeNoTypeFD (ChkFuncDefD z w) impossible
modeNoTypeFD (ChkFunc z w) impossible
modeNoTypeFD (ChkChan z) impossible
modeNoTypeFD (ChkPort z prf) impossible

modeNoTypeC : TyCheck ModuleTyDesc (ChanTy ty) -> Void
modeNoTypeC ChkModule impossible
modeNoTypeC ChkUnit impossible
modeNoTypeC (ChkNat prf) impossible
modeNoTypeC ChkBool impossible
modeNoTypeC (ChkFuncDef x y) impossible
modeNoTypeC (ChkFuncDefD x y) impossible
modeNoTypeC (ChkFunc x y) impossible
modeNoTypeC (ChkChan x) impossible
modeNoTypeC (ChkPort x prf) impossible

modeNoTypePo : TyCheck ModuleTyDesc (PortTy ty dir) -> Void
modeNoTypePo ChkModule impossible
modeNoTypePo ChkUnit impossible
modeNoTypePo (ChkNat prf) impossible
modeNoTypePo ChkBool impossible
modeNoTypePo (ChkFuncDef x y) impossible
modeNoTypePo (ChkFuncDefD x y) impossible
modeNoTypePo (ChkFunc x y) impossible
modeNoTypePo (ChkChan x) impossible
modeNoTypePo (ChkPort x prf) impossible

modeNoTypeN : TyCheck ModuleTyDesc (NatTy n) -> Void
modeNoTypeN ChkModule impossible
modeNoTypeN ChkUnit impossible
modeNoTypeN (ChkNat prf) impossible
modeNoTypeN ChkBool impossible
modeNoTypeN (ChkFuncDef x y) impossible
modeNoTypeN (ChkFuncDefD x y) impossible
modeNoTypeN (ChkFunc x y) impossible
modeNoTypeN (ChkChan x) impossible
modeNoTypeN (ChkPort x prf) impossible

modeNoTypeU : TyCheck ModuleTyDesc UnitTy -> Void
modeNoTypeU ChkModule impossible
modeNoTypeU ChkUnit impossible
modeNoTypeU (ChkNat prf) impossible
modeNoTypeU ChkBool impossible
modeNoTypeU (ChkFuncDef x y) impossible
modeNoTypeU (ChkFuncDefD x y) impossible
modeNoTypeU (ChkFunc x y) impossible
modeNoTypeU (ChkChan x) impossible
modeNoTypeU (ChkPort x prf) impossible

modeNoTypeB : TyCheck ModuleTyDesc BoolTy -> Void
modeNoTypeB ChkModule impossible
modeNoTypeB ChkUnit impossible
modeNoTypeB (ChkNat prf) impossible
modeNoTypeB ChkBool impossible
modeNoTypeB (ChkFuncDef x y) impossible
modeNoTypeB (ChkFuncDefD x y) impossible
modeNoTypeB (ChkFunc x y) impossible
modeNoTypeB (ChkChan x) impossible
modeNoTypeB (ChkPort x prf) impossible

-- ## Channels

chanNotypeF : TyCheck (ChanTyDesc type) (FuncTy x y) -> Void
chanNotypeF ChkModule impossible
chanNotypeF ChkUnit impossible
chanNotypeF (ChkNat prf) impossible
chanNotypeF ChkBool impossible
chanNotypeF (ChkFuncDef z w) impossible
chanNotypeF (ChkFuncDefD z w) impossible
chanNotypeF (ChkFunc z w) impossible
chanNotypeF (ChkChan z) impossible
chanNotypeF (ChkPort z prf) impossible

chanNotypeFD : TyCheck (ChanTyDesc type) (FuncDefTy u x y) -> Void
chanNotypeFD ChkModule impossible
chanNotypeFD ChkUnit impossible
chanNotypeFD (ChkNat prf) impossible
chanNotypeFD ChkBool impossible
chanNotypeFD (ChkFuncDef z w) impossible
chanNotypeFD (ChkFuncDefD z w) impossible
chanNotypeFD (ChkFunc z w) impossible
chanNotypeFD (ChkChan z) impossible
chanNotypeFD (ChkPort z prf) impossible


chanNotypeM  : TyCheck (ChanTyDesc type) ModuleTy -> Void
chanNotypeM ChkModule impossible
chanNotypeM ChkUnit impossible
chanNotypeM (ChkNat prf) impossible
chanNotypeM ChkBool impossible
chanNotypeM (ChkFuncDef x y) impossible
chanNotypeM (ChkFuncDefD x y) impossible
chanNotypeM (ChkFunc x y) impossible
chanNotypeM (ChkChan x) impossible
chanNotypeM (ChkPort x prf) impossible

chanNotypePo : TyCheck (ChanTyDesc type) (PortTy ty dir) -> Void
chanNotypePo ChkModule impossible
chanNotypePo ChkUnit impossible
chanNotypePo (ChkNat prf) impossible
chanNotypePo ChkBool impossible
chanNotypePo (ChkFuncDef x y) impossible
chanNotypePo (ChkFuncDefD x y) impossible
chanNotypePo (ChkFunc x y) impossible
chanNotypePo (ChkChan x) impossible
chanNotypePo (ChkPort x prf) impossible

chanNotypeN : TyCheck (ChanTyDesc x) (NatTy n) -> Void
chanNotypeN ChkModule impossible
chanNotypeN ChkUnit impossible
chanNotypeN (ChkNat prf) impossible
chanNotypeN ChkBool impossible
chanNotypeN (ChkFuncDef y z) impossible
chanNotypeN (ChkFuncDefD y z) impossible
chanNotypeN (ChkFunc y z) impossible
chanNotypeN (ChkChan y) impossible
chanNotypeN (ChkPort y prf) impossible

chanNotypeU  : TyCheck (ChanTyDesc type) UnitTy -> Void
chanNotypeU ChkModule impossible
chanNotypeU ChkUnit impossible
chanNotypeU (ChkNat prf) impossible
chanNotypeU ChkBool impossible
chanNotypeU (ChkFuncDef x y) impossible
chanNotypeU (ChkFuncDefD x y) impossible
chanNotypeU (ChkFunc x y) impossible
chanNotypeU (ChkChan x) impossible
chanNotypeU (ChkPort x prf) impossible

chanNotypeB  : TyCheck (ChanTyDesc type) BoolTy -> Void
chanNotypeB ChkModule impossible
chanNotypeB ChkUnit impossible
chanNotypeB (ChkNat prf) impossible
chanNotypeB ChkBool impossible
chanNotypeB (ChkFuncDef x y) impossible
chanNotypeB (ChkFuncDefD x y) impossible
chanNotypeB (ChkFunc x y) impossible
chanNotypeB (ChkChan x) impossible
chanNotypeB (ChkPort x prf) impossible

chanHasWrongType : (contra : Equals Universe TYPE x y -> Void)
                -> (prf    : TyCheck (ChanTyDesc x) (ChanTy y))
                          -> Void
chanHasWrongType contra (ChkChan (Same Refl Refl)) = contra (Same Refl Refl)


-- ## Ports

portNoTypeF : TyCheck (PortTyDesc type dir) (FuncTy x y) -> Void
portNoTypeF ChkModule impossible
portNoTypeF ChkUnit impossible
portNoTypeF (ChkNat prf) impossible
portNoTypeF ChkBool impossible
portNoTypeF (ChkFuncDef z w) impossible
portNoTypeF (ChkFuncDefD z w) impossible
portNoTypeF (ChkFunc z w) impossible
portNoTypeF (ChkChan z) impossible
portNoTypeF (ChkPort z prf) impossible

portNoTypeFD : TyCheck (PortTyDesc type dir) (FuncDefTy o x y) -> Void
portNoTypeFD ChkModule impossible
portNoTypeFD ChkUnit impossible
portNoTypeFD (ChkNat prf) impossible
portNoTypeFD ChkBool impossible
portNoTypeFD (ChkFuncDef z w) impossible
portNoTypeFD (ChkFuncDefD z w) impossible
portNoTypeFD (ChkFunc z w) impossible
portNoTypeFD (ChkChan z) impossible
portNoTypeFD (ChkPort z prf) impossible

portNoTypeM : TyCheck (PortTyDesc type dir) ModuleTy -> Void
portNoTypeM ChkModule impossible
portNoTypeM ChkUnit impossible
portNoTypeM (ChkNat prf) impossible
portNoTypeM ChkBool impossible
portNoTypeM (ChkFuncDef x y) impossible
portNoTypeM (ChkFuncDefD x y) impossible
portNoTypeM (ChkFunc x y) impossible
portNoTypeM (ChkChan x) impossible
portNoTypeM (ChkPort x prf) impossible

portNoTypeC : TyCheck (PortTyDesc type dir) (ChanTy ty) -> Void
portNoTypeC ChkModule impossible
portNoTypeC ChkUnit impossible
portNoTypeC (ChkNat prf) impossible
portNoTypeC ChkBool impossible
portNoTypeC (ChkFuncDef x y) impossible
portNoTypeC (ChkFuncDefD x y) impossible
portNoTypeC (ChkFunc x y) impossible
portNoTypeC (ChkChan x) impossible
portNoTypeC (ChkPort x prf) impossible

portNoTypeN : TyCheck (PortTyDesc x dir) (NatTy n) -> Void
portNoTypeN ChkModule impossible
portNoTypeN ChkUnit impossible
portNoTypeN (ChkNat prf) impossible
portNoTypeN ChkBool impossible
portNoTypeN (ChkFuncDef y z) impossible
portNoTypeN (ChkFuncDefD y z) impossible
portNoTypeN (ChkFunc y z) impossible
portNoTypeN (ChkChan y) impossible
portNoTypeN (ChkPort y prf) impossible

portNoTypeU : TyCheck (PortTyDesc type dir) UnitTy -> Void
portNoTypeU ChkModule impossible
portNoTypeU ChkUnit impossible
portNoTypeU (ChkNat prf) impossible
portNoTypeU ChkBool impossible
portNoTypeU (ChkFuncDef x y) impossible
portNoTypeU (ChkFuncDefD x y) impossible
portNoTypeU (ChkFunc x y) impossible
portNoTypeU (ChkChan x) impossible
portNoTypeU (ChkPort x prf) impossible

portNoTypeB : TyCheck (PortTyDesc type dir) BoolTy -> Void
portNoTypeB ChkModule impossible
portNoTypeB ChkUnit impossible
portNoTypeB (ChkNat prf) impossible
portNoTypeB ChkBool impossible
portNoTypeB (ChkFuncDef x y) impossible
portNoTypeB (ChkFuncDefD x y) impossible
portNoTypeB (ChkFunc x y) impossible
portNoTypeB (ChkChan x) impossible
portNoTypeB (ChkPort x prf) impossible

portWrongType : (contra : Equals Universe TYPE ty val -> Void)
             -> (prf    : TyCheck (PortTyDesc ty dirT) (PortTy val dirV))
                       -> Void
portWrongType contra (ChkPort (Same Refl Refl) _) = contra (Same Refl Refl)

portWrongDir : (contra : dirT === dirV -> Void)
            -> (prf    : TyCheck (PortTyDesc ty dirT) (PortTy val dirV))
                      -> Void
portWrongDir contra (ChkPort _ Refl) = contra Refl

-- ## Nats

natNoTypeF : TyCheck (NatTyDesc n) (FuncTy param return) -> Void
natNoTypeF ChkModule impossible
natNoTypeF ChkUnit impossible
natNoTypeF (ChkNat prf) impossible
natNoTypeF ChkBool impossible
natNoTypeF (ChkFuncDef x y) impossible
natNoTypeF (ChkFuncDefD x y) impossible
natNoTypeF (ChkFunc x y) impossible
natNoTypeF (ChkChan x) impossible
natNoTypeF (ChkPort x prf) impossible

natNoTypeFD : TyCheck (NatTyDesc n) (FuncDefTy u param return) -> Void
natNoTypeFD ChkModule impossible
natNoTypeFD ChkUnit impossible
natNoTypeFD (ChkNat prf) impossible
natNoTypeFD ChkBool impossible
natNoTypeFD (ChkFuncDef x y) impossible
natNoTypeFD (ChkFuncDefD x y) impossible
natNoTypeFD (ChkFunc x y) impossible
natNoTypeFD (ChkChan x) impossible
natNoTypeFD (ChkPort x prf) impossible

natNoTypeC : TyCheck (NatTyDesc n) (ChanTy x) -> Void
natNoTypeC ChkModule impossible
natNoTypeC ChkUnit impossible
natNoTypeC (ChkNat prf) impossible
natNoTypeC ChkBool impossible
natNoTypeC (ChkFuncDef y z) impossible
natNoTypeC (ChkFuncDefD y z) impossible
natNoTypeC (ChkFunc y z) impossible
natNoTypeC (ChkChan y) impossible
natNoTypeC (ChkPort y prf) impossible

natNoTypeM : TyCheck (NatTyDesc n) ModuleTy -> Void
natNoTypeM ChkModule impossible
natNoTypeM ChkUnit impossible
natNoTypeM (ChkNat prf) impossible
natNoTypeM ChkBool impossible
natNoTypeM (ChkFuncDef x y) impossible
natNoTypeM (ChkFuncDefD x y) impossible
natNoTypeM (ChkFunc x y) impossible
natNoTypeM (ChkChan x) impossible
natNoTypeM (ChkPort x prf) impossible

natNoTypeP : TyCheck (NatTyDesc n) (PortTy x dir) -> Void
natNoTypeP ChkModule impossible
natNoTypeP ChkUnit impossible
natNoTypeP (ChkNat prf) impossible
natNoTypeP ChkBool impossible
natNoTypeP (ChkFuncDef y z) impossible
natNoTypeP (ChkFuncDefD y z) impossible
natNoTypeP (ChkFunc y z) impossible
natNoTypeP (ChkChan y) impossible
natNoTypeP (ChkPort y prf) impossible

natNoTypeU : TyCheck (NatTyDesc n) UnitTy -> Void
natNoTypeU ChkModule impossible
natNoTypeU ChkUnit impossible
natNoTypeU (ChkNat prf) impossible
natNoTypeU ChkBool impossible
natNoTypeU (ChkFuncDef x y) impossible
natNoTypeU (ChkFuncDefD x y) impossible
natNoTypeU (ChkFunc x y) impossible
natNoTypeU (ChkChan x) impossible
natNoTypeU (ChkPort x prf) impossible

natNoTypeB : TyCheck (NatTyDesc n) BoolTy -> Void
natNoTypeB ChkModule impossible
natNoTypeB ChkUnit impossible
natNoTypeB (ChkNat prf) impossible
natNoTypeB ChkBool impossible
natNoTypeB (ChkFuncDef x y) impossible
natNoTypeB (ChkFuncDefD x y) impossible
natNoTypeB (ChkFunc x y) impossible
natNoTypeB (ChkChan x) impossible
natNoTypeB (ChkPort x prf) impossible

natNoWrongNat : (n = m -> Void) -> TyCheck (NatTyDesc n) (NatTy m) -> Void
natNoWrongNat f (ChkNat Refl) = f Refl

-- ## Unit

unitNoTypeF : TyCheck UnitTyDesc (FuncTy x y) -> Void
unitNoTypeF ChkModule impossible
unitNoTypeF ChkUnit impossible
unitNoTypeF (ChkNat prf) impossible
unitNoTypeF ChkBool impossible
unitNoTypeF (ChkFuncDef z w) impossible
unitNoTypeF (ChkFuncDefD z w) impossible
unitNoTypeF (ChkFunc z w) impossible
unitNoTypeF (ChkChan z) impossible
unitNoTypeF (ChkPort z prf) impossible

unitNoTypeFD : TyCheck UnitTyDesc (FuncDefTy u x y) -> Void
unitNoTypeFD ChkModule impossible
unitNoTypeFD ChkUnit impossible
unitNoTypeFD (ChkNat prf) impossible
unitNoTypeFD ChkBool impossible
unitNoTypeFD (ChkFuncDef z w) impossible
unitNoTypeFD (ChkFuncDefD z w) impossible
unitNoTypeFD (ChkFunc z w) impossible
unitNoTypeFD (ChkChan z) impossible
unitNoTypeFD (ChkPort z prf) impossible

unitNoTypeM : TyCheck UnitTyDesc ModuleTy -> Void
unitNoTypeM ChkModule impossible
unitNoTypeM ChkUnit impossible
unitNoTypeM (ChkNat prf) impossible
unitNoTypeM ChkBool impossible
unitNoTypeM (ChkFuncDef x y) impossible
unitNoTypeM (ChkFuncDefD x y) impossible
unitNoTypeM (ChkFunc x y) impossible
unitNoTypeM (ChkChan x) impossible
unitNoTypeM (ChkPort x prf) impossible

unitNoTypeC : TyCheck UnitTyDesc (ChanTy t) -> Void
unitNoTypeC ChkModule impossible
unitNoTypeC ChkUnit impossible
unitNoTypeC (ChkNat prf) impossible
unitNoTypeC ChkBool impossible
unitNoTypeC (ChkFuncDef x y) impossible
unitNoTypeC (ChkFuncDefD x y) impossible
unitNoTypeC (ChkFunc x y) impossible
unitNoTypeC (ChkChan x) impossible
unitNoTypeC (ChkPort x prf) impossible

unitNoTypePo : TyCheck UnitTyDesc (PortTy x dir) -> Void
unitNoTypePo ChkModule impossible
unitNoTypePo ChkUnit impossible
unitNoTypePo (ChkNat prf) impossible
unitNoTypePo ChkBool impossible
unitNoTypePo (ChkFuncDef y z) impossible
unitNoTypePo (ChkFuncDefD y z) impossible
unitNoTypePo (ChkFunc y z) impossible
unitNoTypePo (ChkChan y) impossible
unitNoTypePo (ChkPort y prf) impossible

unitNoTypeN : TyCheck UnitTyDesc (NatTy n) -> Void
unitNoTypeN ChkModule impossible
unitNoTypeN ChkUnit impossible
unitNoTypeN (ChkNat prf) impossible
unitNoTypeN ChkBool impossible
unitNoTypeN (ChkFuncDef x y) impossible
unitNoTypeN (ChkFuncDefD x y) impossible
unitNoTypeN (ChkFunc x y) impossible
unitNoTypeN (ChkChan x) impossible
unitNoTypeN (ChkPort x prf) impossible

unitNoTypeB : TyCheck UnitTyDesc BoolTy -> Void
unitNoTypeB ChkModule impossible
unitNoTypeB ChkUnit impossible
unitNoTypeB (ChkNat prf) impossible
unitNoTypeB ChkBool impossible
unitNoTypeB (ChkFuncDef x y) impossible
unitNoTypeB (ChkFuncDefD x y) impossible
unitNoTypeB (ChkFunc x y) impossible
unitNoTypeB (ChkChan x) impossible
unitNoTypeB (ChkPort x prf) impossible

-- ## Booleans

boolNoTypeF : TyCheck BoolTyDesc (FuncTy x y) -> Void
boolNoTypeF ChkModule impossible
boolNoTypeF ChkUnit impossible
boolNoTypeF (ChkNat prf) impossible
boolNoTypeF ChkBool impossible
boolNoTypeF (ChkFuncDef z w) impossible
boolNoTypeF (ChkFuncDefD z w) impossible
boolNoTypeF (ChkFunc z w) impossible
boolNoTypeF (ChkChan z) impossible
boolNoTypeF (ChkPort z prf) impossible

boolNoTypeFD : TyCheck BoolTyDesc (FuncDefTy u x y) -> Void
boolNoTypeFD ChkModule impossible
boolNoTypeFD ChkUnit impossible
boolNoTypeFD (ChkNat prf) impossible
boolNoTypeFD ChkBool impossible
boolNoTypeFD (ChkFuncDef z w) impossible
boolNoTypeFD (ChkFuncDefD z w) impossible
boolNoTypeFD (ChkFunc z w) impossible
boolNoTypeFD (ChkChan z) impossible
boolNoTypeFD (ChkPort z prf) impossible

boolNoTypeM : TyCheck BoolTyDesc ModuleTy -> Void
boolNoTypeM ChkModule impossible
boolNoTypeM ChkUnit impossible
boolNoTypeM (ChkNat prf) impossible
boolNoTypeM ChkBool impossible
boolNoTypeM (ChkFuncDef x y) impossible
boolNoTypeM (ChkFuncDefD x y) impossible
boolNoTypeM (ChkFunc x y) impossible
boolNoTypeM (ChkChan x) impossible
boolNoTypeM (ChkPort x prf) impossible

boolNoTypeU : TyCheck BoolTyDesc UnitTy -> Void
boolNoTypeU ChkModule impossible
boolNoTypeU ChkUnit impossible
boolNoTypeU (ChkNat prf) impossible
boolNoTypeU ChkBool impossible
boolNoTypeU (ChkFuncDef x y) impossible
boolNoTypeU (ChkFuncDefD x y) impossible
boolNoTypeU (ChkFunc x y) impossible
boolNoTypeU (ChkChan x) impossible
boolNoTypeU (ChkPort x prf) impossible

boolNoTypeC : TyCheck BoolTyDesc (ChanTy t) -> Void
boolNoTypeC ChkModule impossible
boolNoTypeC ChkUnit impossible
boolNoTypeC (ChkNat prf) impossible
boolNoTypeC ChkBool impossible
boolNoTypeC (ChkFuncDef x y) impossible
boolNoTypeC (ChkFuncDefD x y) impossible
boolNoTypeC (ChkFunc x y) impossible
boolNoTypeC (ChkChan x) impossible
boolNoTypeC (ChkPort x prf) impossible

boolNoTypePo : TyCheck BoolTyDesc (PortTy x dir) -> Void
boolNoTypePo ChkModule impossible
boolNoTypePo ChkUnit impossible
boolNoTypePo (ChkNat prf) impossible
boolNoTypePo ChkBool impossible
boolNoTypePo (ChkFuncDef y z) impossible
boolNoTypePo (ChkFuncDefD y z) impossible
boolNoTypePo (ChkFunc y z) impossible
boolNoTypePo (ChkChan y) impossible
boolNoTypePo (ChkPort y prf) impossible

boolNoTypeN : TyCheck BoolTyDesc (NatTy n) -> Void
boolNoTypeN ChkModule impossible
boolNoTypeN ChkUnit impossible
boolNoTypeN (ChkNat prf) impossible
boolNoTypeN ChkBool impossible
boolNoTypeN (ChkFuncDef x y) impossible
boolNoTypeN (ChkFuncDefD x y) impossible
boolNoTypeN (ChkFunc x y) impossible
boolNoTypeN (ChkChan x) impossible
boolNoTypeN (ChkPort x prf) impossible

-- ## Func Def

funcDefInvalidParam : (u = DATA TYPE -> Void)
                   -> (u = IDX TYPE -> Void)
                   -> TyCheck (FuncDefTy u x y) (FuncDefTy v z w)
                   -> Void
funcDefInvalidParam f g (ChkFuncDef s t) = g Refl
funcDefInvalidParam f g (ChkFuncDefD z s) = f Refl

funcDefParamDataNotBothSame : (v = DATA TYPE -> Void)
                            -> TyCheck (FuncDefTy (DATA TYPE) x y) (FuncDefTy v z w)
                            -> Void
funcDefParamDataNotBothSame f (ChkFuncDefD z s) = f Refl

funcDefInvalidTypeDataTerm : (IDX TERM = v -> Void)
                           -> TyCheck (FuncDefTy (IDX TYPE) x y) (FuncDefTy v z w)
                           -> Void
funcDefInvalidTypeDataTerm g (ChkFuncDef s t) = g Refl


funcDefInvalidTypeData : (IDX TYPE = DATA TYPE -> Void)
                      -> (TyCheck y w -> Void)
                      -> TyCheck (FuncDefTy (IDX TYPE) x y) (FuncDefTy (IDX TERM) z w)
                      -> Void
funcDefInvalidTypeData f g (ChkFuncDef v s) = g s

funcDefExpectedDataType : (TyCheck x z -> Void)
                        -> TyCheck (FuncDefTy (IDX TYPE) x y) (FuncDefTy (IDX TERM) z w)
                        -> Void
funcDefExpectedDataType f (ChkFuncDef v s) = f v

funcDefDataTypesNotEqual : (Equals Universe TYPE x z -> Void)
                         -> TyCheck (FuncDefTy (DATA TYPE) x y) (FuncDefTy (DATA TYPE) z w)
                         -> Void
funcDefDataTypesNotEqual f (ChkFuncDefD z v) = f (Same Refl Refl)

funcDefParamSomething : (TyCheck y w -> Void)
                      -> TyCheck (FuncDefTy (DATA TYPE) x y) (FuncDefTy (DATA TYPE) x w)
                      -> Void
funcDefParamSomething f (ChkFuncDefD x z) = f z

-- ## Type Checking

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

    typeCheck type value | (FuncTy x y) | BoolTy
      = No (WrongType type value) (funcNoTypeB)

    typeCheck type value | (FuncTy x y) | (FuncDefTy i a r)
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
    typeCheck type value | ModuleTyDesc | (NatTy n)
      = No (WrongType type value) (modeNoTypeN)
    typeCheck type value | ModuleTyDesc | UnitTy
      = No (WrongType type value) (modeNoTypeU)
    typeCheck type value | ModuleTyDesc | BoolTy
      = No (WrongType type value) (modeNoTypeB)
    typeCheck type value | ModuleTyDesc | (FuncDefTy u a r)
      = No (WrongType type value) (modeNoTypeFD)

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
    typeCheck type value | (ChanTyDesc x) | BoolTy
      = No (WrongType type value) (chanNotypeB)
    typeCheck type value | (ChanTyDesc x) | (FuncDefTy i a r)
      = No (WrongType type value) (chanNotypeFD)

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
    typeCheck type value | (PortTyDesc x dir) | BoolTy
      = No (WrongType type value) (portNoTypeB)
    typeCheck type value | (PortTyDesc x dir) | (FuncDefTy u a r)
      = No (WrongType type value) (portNoTypeFD)

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
    typeCheck type value | (NatTyDesc n) | BoolTy
      = No (WrongType type value) natNoTypeB
    typeCheck type value | (NatTyDesc n) | (FuncDefTy u a r)
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
    typeCheck type value | UnitTyDesc | (NatTy n)
      = No (WrongType type value) (unitNoTypeN)
    typeCheck type value | UnitTyDesc | UnitTy
      = Yes ChkUnit
    typeCheck type value | UnitTyDesc | BoolTy
      = No (WrongType type value) unitNoTypeB

    typeCheck type value | UnitTyDesc | (FuncDefTy u a r)
      = No (WrongType type value) unitNoTypeFD

  typeCheck type value | (FuncDefTy u x y) with (value)
    typeCheck type value | (FuncDefTy u x y) | (FuncTy a r)
      = No (WrongType type value) (funcDefNoTypeF)

    typeCheck type value | (FuncDefTy u x y) | ModuleTy
      = No (WrongType type value) (funcDefNoTypeM)
    typeCheck type value | (FuncDefTy u x y) | (ChanTy z)
      = No (WrongType type value) (funcDefNoTypeC)
    typeCheck type value | (FuncDefTy u x y) | (PortTy z dir)
      = No (WrongType type value) (funcDefNoTypePo)
    typeCheck type value | (FuncDefTy u x y) | (NatTy n)
      = No (WrongType type value) (funcDefNoTypeN)
    typeCheck type value | (FuncDefTy u x y) | UnitTy
      = No (WrongType type value) (funcDefNoTypeU)
    typeCheck type value | (FuncDefTy u x y) | (FuncDefTy v z w) with (Universe.decEq u (DATA TYPE))

      typeCheck type value | (FuncDefTy u x y) | (FuncDefTy v z w) | (Yes prfDataTy) with (prfDataTy)
        typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy v z w) | (Yes prfDataTy) | Refl with (Universe.decEq v (DATA TYPE))
          typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy v z w) | (Yes prfDataTy) | Refl | (Yes prf) with (prf)
            typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy (DATA TYPE) z w) | (Yes prfDataTy) | Refl | (Yes prf) | Refl with (Equality.decEq x z)
              typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy (DATA TYPE) z w) | (Yes prfDataTy) | Refl | (Yes prf) | Refl | (Yes prfWhy) with (prfWhy)
                typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy (DATA TYPE) x w) | (Yes prfDataTy) | Refl | (Yes prf) | Refl | (Yes prfWhy) | (Same Refl Refl) with (typeCheck y w)
                  typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy (DATA TYPE) x w) | (Yes prfDataTy) | Refl | (Yes prf) | Refl | (Yes prfWhy) | (Same Refl Refl) | (Yes z)
                    = Yes (ChkFuncDefD x z)
                  typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy (DATA TYPE) x w) | (Yes prfDataTy) | Refl | (Yes prf) | Refl | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
                    = No (WrongType type value) (funcDefParamSomething prfWhyNot)

              typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy (DATA TYPE) z w) | (Yes prfDataTy) | Refl | (Yes prf) | Refl | (No msgWhyNot prfWhyNot)
                = No (WrongType type value) (funcDefDataTypesNotEqual prfWhyNot)

          typeCheck type value | (FuncDefTy (DATA TYPE) x y) | (FuncDefTy v z w) | (Yes prfDataTy) | Refl | (No bothMustBeData)
            = No (WrongType type value) (funcDefParamDataNotBothSame bothMustBeData)

      typeCheck type value | (FuncDefTy u x y) | (FuncDefTy v z w) | (No notDataType) with (Universe.decEq u (IDX TYPE))

        typeCheck type value | (FuncDefTy u x y) | (FuncDefTy v z w) | (No notDataType) | (Yes prf) with (prf)
          typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy v z w) | (No notDataType) | (Yes prf) | Refl with (Equality.decEq (IDX TERM) v)
            typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy v z w) | (No notDataType) | (Yes prf) | Refl | (Yes s) with (s)
              typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy (IDX TERM) z w) | (No notDataType) | (Yes prf) | Refl | (Yes s) | Refl with (typeCheck x z)
                typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy (IDX TERM) z w) | (No notDataType) | (Yes prf) | Refl | (Yes s) | Refl | (Yes prfWhy) with (typeCheck y w)
                  typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy (IDX TERM) z w) | (No notDataType) | (Yes prf) | Refl | (Yes s) | Refl | (Yes prfWhy) | (Yes v)
                    = Yes (ChkFuncDef prfWhy v)
                  typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy (IDX TERM) z w) | (No notDataType) | (Yes prf) | Refl | (Yes s) | Refl | (Yes prfWhy) | (No msgWhyNot prfWhyNot)
                    = No (WrongType type value) (funcDefInvalidTypeData notDataType prfWhyNot)

                typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy (IDX TERM) z w) | (No notDataType) | (Yes prf) | Refl | (Yes s) | Refl | (No msgWhyNot prfWhyNot)
                  = No (WrongType type value) (funcDefExpectedDataType prfWhyNot)

            typeCheck type value | (FuncDefTy (IDX TYPE) x y) | (FuncDefTy v z w) | (No notDataType) | (Yes prf) | Refl | (No contra)
              = No (WrongType type value) (funcDefInvalidTypeDataTerm contra)

        typeCheck type value | (FuncDefTy u x y) | (FuncDefTy v z w) | (No notDataType) | (No notTypeType)
          = No (WrongType type value) (funcDefInvalidParam notDataType notTypeType)

    typeCheck type value | (FuncDefTy u x y) | BoolTy
      = No (WrongType type value) (funcDefNoTypeB)


  typeCheck type value | BoolTyDesc with (value)
    typeCheck type value | BoolTyDesc | (FuncTy param return)
      = No (WrongType type value) boolNoTypeF
    typeCheck type value | BoolTyDesc | (FuncDefTy u param return)
      = No (WrongType type value) boolNoTypeFD
    typeCheck type value | BoolTyDesc | ModuleTy
      = No (WrongType type value) boolNoTypeM
    typeCheck type value | BoolTyDesc | (ChanTy x)
      = No (WrongType type value) boolNoTypeC
    typeCheck type value | BoolTyDesc | (PortTy x dir)
      = No (WrongType type value) boolNoTypePo
    typeCheck type value | BoolTyDesc | UnitTy
      = No (WrongType type value) boolNoTypeU
    typeCheck type value | BoolTyDesc | (NatTy k)
      = No (WrongType type value) boolNoTypeN

    typeCheck type value | BoolTyDesc | BoolTy
      = Yes ChkBool

public export
data CheckedNat : (TyCheck type value) -> Type where
  IsCheckedNat : CheckedNat (ChkNat Refl)

isBool : CheckedNat ChkBool -> Void
isBool IsCheckedNat impossible

isC : CheckedNat (ChkChan x) -> Void
isC IsCheckedNat impossible

isF : CheckedNat (ChkFunc x y) -> Void
isF IsCheckedNat impossible

isFDef : CheckedNat (ChkFuncDef x y) -> Void
isFDef IsCheckedNat impossible

isFDefD : CheckedNat (ChkFuncDefD paramTy x) -> Void
isFDefD IsCheckedNat impossible

isModule : CheckedNat ChkModule -> Void
isModule IsCheckedNat impossible

isP : CheckedNat (ChkPort x prf) -> Void
isP IsCheckedNat impossible

isUnit : CheckedNat ChkUnit -> Void
isUnit IsCheckedNat impossible

export
isCheckedNat : (prf : TyCheck type value) -> Dec (CheckedNat prf)
isCheckedNat (ChkNat Refl) = Yes IsCheckedNat

isCheckedNat ChkModule = No isModule
isCheckedNat ChkUnit = No isUnit

isCheckedNat ChkBool = No isBool
isCheckedNat (ChkFuncDef x y) = No isFDef
isCheckedNat (ChkFuncDefD paramTy x) = No isFDefD
isCheckedNat (ChkFunc x y) = No isF
isCheckedNat (ChkChan x) = No isC
isCheckedNat (ChkPort x prf) = No isP

-- [ EOF ]
