module SystemV.Param.Types.TYPE.Equality.Types.Terms

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE

%default total

export
funcTypeTyNotModuleTy : (Equals Universe TYPE (FuncTy x y) ModuleTy)
                             -> Void
funcTypeTyNotModuleTy (Same Refl Refl) impossible

export
funcTypeTyNotChanTy : (Equals Universe TYPE (FuncTy x y) (ChanTy t))
                           -> Void
funcTypeTyNotChanTy (Same Refl Refl) impossible

export
funcTypeTyNotPortTy : (Equals Universe TYPE (FuncTy x y) (PortTy t d))
                           -> Void
funcTypeTyNotPortTy (Same Refl Refl) impossible

export
funcTypeTyNotNatTy : (Equals Universe TYPE (FuncTy x y) NatTy)
                           -> Void
funcTypeTyNotNatTy (Same Refl Refl) impossible

export
funcTypeTyNotUnitTy : (Equals Universe TYPE (FuncTy x y) UnitTy)
                           -> Void
funcTypeTyNotUnitTy (Same Refl Refl) impossible

export
funcTypeTyNotBoolTy : (Equals Universe TYPE (FuncTy x y) BoolTy)
                           -> Void
funcTypeTyNotBoolTy (Same Refl Refl) impossible

export
funcTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                               -> Equals Universe TYPE (FuncTy x a) (FuncTy y b)
                               -> Void
funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                -> Equals Universe TYPE (FuncTy x a) (FuncTy x b)
                                -> Void
funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcTypeNotFuncParamType : (Equals Universe TYPE (FuncTy x y) (FuncParamTy u a b))
                                   -> Void
funcTypeNotFuncParamType (Same Refl Refl) impossible

export
moduleTyNotChanTy : Equals Universe TYPE (ModuleTy) (ChanTy type) -> Void
moduleTyNotChanTy (Same Refl Refl) impossible

export
moduleTyNotPortTy : Equals Universe TYPE (ModuleTy) (PortTy type dir) -> Void
moduleTyNotPortTy (Same Refl Refl) impossible

export
moduleTyNotNatTy : Equals Universe TYPE (ModuleTy) NatTy -> Void
moduleTyNotNatTy (Same Refl Refl) impossible

export
moduleTyNotUnitTy : Equals Universe TYPE (ModuleTy) UnitTy -> Void
moduleTyNotUnitTy (Same Refl Refl) impossible

export
moduleTyNotBoolTy : Equals Universe TYPE (ModuleTy) BoolTy -> Void
moduleTyNotBoolTy (Same Refl Refl) impossible

export
moduleNotFuncParam : Equals Universe TYPE (ModuleTy) (FuncParamTy u a b) -> Void
moduleNotFuncParam (Same Refl Refl) impossible

export
chanTyNotPortTy : Equals Universe TYPE (ChanTy type) (PortTy t d) -> Void
chanTyNotPortTy (Same Refl Refl) impossible

export
chanTyNotNatTy : Equals Universe TYPE (ChanTy type) NatTy -> Void
chanTyNotNatTy (Same Refl Refl) impossible

export
chanTyNotUnitTy : Equals Universe TYPE (ChanTy type) UnitTy -> Void
chanTyNotUnitTy (Same Refl Refl) impossible

export
chanTyNotBoolTy : Equals Universe TYPE (ChanTy type) BoolTy -> Void
chanTyNotBoolTy (Same Refl Refl) impossible

export
chanTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTy x) (ChanTy y))
                             -> Void
chanTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
chanNotFuncParam : Equals Universe TYPE (ChanTy type) (FuncParamTy u t d) -> Void
chanNotFuncParam (Same Refl Refl) impossible

export
portTyNotNatTy : Equals Universe TYPE (PortTy type dir) NatTy -> Void
portTyNotNatTy (Same Refl Refl) impossible

export
portTyNotUnitTy : Equals Universe TYPE (PortTy type dir) UnitTy -> Void
portTyNotUnitTy (Same Refl Refl) impossible

export
portTyNotBoolTy : Equals Universe TYPE (PortTy type dir) BoolTy -> Void
portTyNotBoolTy (Same Refl Refl) impossible

export
portTyDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTy x a) (PortTy y b))
                             -> Void
portTyDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
portTyDiffDirs : (contra : a === b -> Void)
                  -> (prf   : Equals Universe TYPE (PortTy type a) (PortTy x b))
                           -> Void
portTyDiffDirs contra (Same Refl Refl) = contra Refl

export
portNotFuncParam : Equals Universe TYPE (PortTy type dir) (FuncParamTy u x y) -> Void
portNotFuncParam (Same Refl Refl) impossible

export
natNotFuncParam : Equals Universe TYPE NatTy (FuncParamTy u x y) -> Void
natNotFuncParam (Same Refl Refl) impossible

export
natTyNotUnitTy : Equals Universe TYPE NatTy UnitTy -> Void
natTyNotUnitTy (Same Refl Refl) impossible

export
natTyNotBoolTy : Equals Universe TYPE NatTy BoolTy -> Void
natTyNotBoolTy (Same Refl Refl) impossible

export
unitTyNotFuncParamTy : Equals Universe TYPE UnitTy (FuncParamTy u x y) -> Void
unitTyNotFuncParamTy (Same Refl Refl) impossible

export
unitTyNotBoolTy : Equals Universe TYPE UnitTy BoolTy -> Void
unitTyNotBoolTy (Same Refl Refl) impossible

export
funcParamTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                                  -> Equals Universe TYPE (FuncParamTy u x a) (FuncParamTy u y b)
                                  -> Void
funcParamTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcParamTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                   -> Equals Universe TYPE (FuncParamTy u x a) (FuncParamTy u x b)
                                   -> Void
funcParamTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcParamTypeNotBoolTy : Equals Universe TYPE (FuncParamTy u p r) BoolTy -> Void
funcParamTypeNotBoolTy (Same Refl Refl) impossible

-- [ EOF ]
