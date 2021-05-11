module SystemV.Param.Types.TYPE.Equality.Types.Types

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Param.Types.TYPE

%default total

export
funcTypeTyDescNotModuleTyDesc : (Equals Universe TYPE (FuncTy x y) ModuleTyDesc)
                             -> Void
funcTypeTyDescNotModuleTyDesc (Same Refl Refl) impossible

export
funcTypeTyDescNotChanTyDesc : (Equals Universe TYPE (FuncTy x y) (ChanTyDesc t))
                           -> Void
funcTypeTyDescNotChanTyDesc (Same Refl Refl) impossible

export
funcTypeTyDescNotPortTyDesc : (Equals Universe TYPE (FuncTy x y) (PortTyDesc t d))
                           -> Void
funcTypeTyDescNotPortTyDesc (Same Refl Refl) impossible

export
funcTypeTyDescNotUnitTyDesc : (Equals Universe TYPE (FuncTy x y) UnitTyDesc)
                           -> Void
funcTypeTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
funcTypeTyDescNotNatTyDesc : (Equals Universe TYPE (FuncTy x y) NatTyDesc)
                           -> Void
funcTypeTyDescNotNatTyDesc (Same Refl Refl) impossible

export
funcTypeTyDescNotBoolTyDesc : (Equals Universe TYPE (FuncTy x y) BoolTyDesc)
                           -> Void
funcTypeTyDescNotBoolTyDesc (Same Refl Refl) impossible

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
funcTypeTyDescNotFuncParamTypeTyDesc : (Equals Universe TYPE (FuncTy x y) (FuncParamTy u a b))
                                   -> Void
funcTypeTyDescNotFuncParamTypeTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotFuncParamTyDesc : Equals Universe TYPE (ModuleTyDesc) (FuncParamTy u a b) -> Void
moduleTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotChanTyDesc : Equals Universe TYPE (ModuleTyDesc) (ChanTyDesc type) -> Void
moduleTyDescNotChanTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotPortTyDesc : Equals Universe TYPE (ModuleTyDesc) (PortTyDesc type dir) -> Void
moduleTyDescNotPortTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotUnitTyDesc : Equals Universe TYPE (ModuleTyDesc) UnitTyDesc -> Void
moduleTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotNatTyDesc : Equals Universe TYPE (ModuleTyDesc) NatTyDesc -> Void
moduleTyDescNotNatTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotBoolTyDesc : Equals Universe TYPE (ModuleTyDesc) BoolTyDesc -> Void
moduleTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
chanTyDescNotPortTyDesc : Equals Universe TYPE (ChanTyDesc type) (PortTyDesc t d) -> Void
chanTyDescNotPortTyDesc (Same Refl Refl) impossible

export
chanTyDescNotUnitTyDesc : Equals Universe TYPE (ChanTyDesc type) UnitTyDesc -> Void
chanTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
chanTyDescNotNatTyDesc : Equals Universe TYPE (ChanTyDesc type) NatTyDesc -> Void
chanTyDescNotNatTyDesc (Same Refl Refl) impossible

export
chanTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTyDesc x) (ChanTyDesc y))
                             -> Void
chanTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
chanTyDescNotFuncParamTyDesc : Equals Universe TYPE (ChanTyDesc type) (FuncParamTy u t d) -> Void
chanTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
chanTyDescNotBoolTyDesc : Equals Universe TYPE (ChanTyDesc type) BoolTyDesc -> Void
chanTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
portTyDescNotUnitTyDesc : Equals Universe TYPE (PortTyDesc type dir) UnitTyDesc -> Void
portTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
portTyDescNotNatTyDesc : Equals Universe TYPE (PortTyDesc type dir) NatTyDesc -> Void
portTyDescNotNatTyDesc (Same Refl Refl) impossible

export
portTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (PortTyDesc x a) (PortTyDesc y b))
                             -> Void
portTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
portTyDescDiffDirs : (contra : a === b -> Void)
                  -> (prf    : Equals Universe TYPE (PortTyDesc x a) (PortTyDesc x b))
                            -> Void
portTyDescDiffDirs contra (Same Refl Refl) = contra Refl

export
portTyDescNotFuncParamTyDesc : Equals Universe TYPE (PortTyDesc type dir) (FuncParamTy u x y) -> Void
portTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
portTyDescNotBoolTyDesc : Equals Universe TYPE (PortTyDesc type dir) BoolTyDesc -> Void
portTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
natTyDescNotUnitTyDesc : Equals Universe TYPE NatTyDesc UnitTyDesc -> Void
natTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
natTyDescNotFuncParamTyDesc : Equals Universe TYPE NatTyDesc (FuncParamTy u x y) -> Void
natTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
natTyDescNotBoolTyDesc : Equals Universe TYPE NatTyDesc BoolTyDesc -> Void
natTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
unitTyDescNotFuncParamTyDesc : Equals Universe TYPE UnitTyDesc (FuncParamTy u x y) -> Void
unitTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
unitTyDescNotBoolTyDesc : Equals Universe TYPE UnitTyDesc BoolTyDesc -> Void
unitTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
funcParamTyParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                                  -> Equals Universe TYPE (FuncParamTy u x a) (FuncParamTy u y b)
                                  -> Void
funcParamTyParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcParamTyReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                   -> Equals Universe TYPE (FuncParamTy u x a) (FuncParamTy u x b)
                                   -> Void
funcParamTyReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcParamTyNotBoolTyDesc : Equals Universe TYPE (FuncParamTy u p r) BoolTyDesc -> Void
funcParamTyNotBoolTyDesc (Same Refl Refl) impossible


-- [ EOF ]
