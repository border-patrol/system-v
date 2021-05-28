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
funcTypeTyDescNotChanTyDesc : (Equals Universe TYPE (FuncTy x y) (ChanTyDesc))
                           -> Void
funcTypeTyDescNotChanTyDesc (Same Refl Refl) impossible

export
funcTypeTyDescNotPortTyDesc : (Equals Universe TYPE (FuncTy x y) (PortTyDesc d))
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
moduleTyDescNotChanTyDesc : Equals Universe TYPE (ModuleTyDesc) ChanTyDesc -> Void
moduleTyDescNotChanTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotPortTyDesc : Equals Universe TYPE (ModuleTyDesc) (PortTyDesc dir) -> Void
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
chanTyDescNotPortTyDesc : Equals Universe TYPE ChanTyDesc (PortTyDesc d) -> Void
chanTyDescNotPortTyDesc (Same Refl Refl) impossible

export
chanTyDescNotUnitTyDesc : Equals Universe TYPE ChanTyDesc UnitTyDesc -> Void
chanTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
chanTyDescNotNatTyDesc : Equals Universe TYPE ChanTyDesc NatTyDesc -> Void
chanTyDescNotNatTyDesc (Same Refl Refl) impossible

export
chanTyDescNotFuncParamTyDesc : Equals Universe TYPE ChanTyDesc (FuncParamTy u t d) -> Void
chanTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
chanTyDescNotBoolTyDesc : Equals Universe TYPE ChanTyDesc BoolTyDesc -> Void
chanTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
portTyDescNotUnitTyDesc : Equals Universe TYPE (PortTyDesc dir) UnitTyDesc -> Void
portTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
portTyDescNotNatTyDesc : Equals Universe TYPE (PortTyDesc dir) NatTyDesc -> Void
portTyDescNotNatTyDesc (Same Refl Refl) impossible

export
portTyDescDiffDirs : (contra : a === b -> Void)
                  -> (prf    : Equals Universe TYPE (PortTyDesc a) (PortTyDesc b))
                            -> Void
portTyDescDiffDirs contra (Same Refl Refl) = contra Refl

export
portTyDescNotFuncParamTyDesc : Equals Universe TYPE (PortTyDesc dir) (FuncParamTy u x y) -> Void
portTyDescNotFuncParamTyDesc (Same Refl Refl) impossible

export
portTyDescNotBoolTyDesc : Equals Universe TYPE (PortTyDesc dir) BoolTyDesc -> Void
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
