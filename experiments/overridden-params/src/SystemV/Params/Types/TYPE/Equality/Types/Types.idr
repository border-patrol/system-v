module SystemV.Params.Types.TYPE.Equality.Types.Types

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Params.Types.TYPE

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
funcTypeTyDescNotNatTyDesc : (Equals Universe TYPE (FuncTy x y) (NatTyDesc n))
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
funcTypeTyDescNotFuncDefTypeTyDesc : (Equals Universe TYPE (FuncTy x y) (FuncDefTy u a b))
                                   -> Void
funcTypeTyDescNotFuncDefTypeTyDesc (Same Refl Refl) impossible

export
moduleTyDescNotFuncDefTyDesc : Equals Universe TYPE (ModuleTyDesc) (FuncDefTy u a b) -> Void
moduleTyDescNotFuncDefTyDesc (Same Refl Refl) impossible

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
moduleTyDescNotNatTyDesc : Equals Universe TYPE (ModuleTyDesc) (NatTyDesc n) -> Void
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
chanTyDescNotNatTyDesc : Equals Universe TYPE (ChanTyDesc type) (NatTyDesc n) -> Void
chanTyDescNotNatTyDesc (Same Refl Refl) impossible

export
chanTyDescDiffTypes : (contra : Equals Universe TYPE x y -> Void)
                   -> (prf    : Equals Universe TYPE (ChanTyDesc x) (ChanTyDesc y))
                             -> Void
chanTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

export
chanTyDescNotFuncDefTyDesc : Equals Universe TYPE (ChanTyDesc type) (FuncDefTy u t d) -> Void
chanTyDescNotFuncDefTyDesc (Same Refl Refl) impossible

export
chanTyDescNotBoolTyDesc : Equals Universe TYPE (ChanTyDesc type) BoolTyDesc -> Void
chanTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
portTyDescNotUnitTyDesc : Equals Universe TYPE (PortTyDesc type dir) UnitTyDesc -> Void
portTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
portTyDescNotNatTyDesc : Equals Universe TYPE (PortTyDesc type dir) (NatTyDesc n) -> Void
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
portTyDescNotFuncDefTyDesc : Equals Universe TYPE (PortTyDesc type dir) (FuncDefTy u x y) -> Void
portTyDescNotFuncDefTyDesc (Same Refl Refl) impossible

export
portTyDescNotBoolTyDesc : Equals Universe TYPE (PortTyDesc type dir) BoolTyDesc -> Void
portTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
natTyDescNotUnitTyDesc : Equals Universe TYPE (NatTyDesc n) UnitTyDesc -> Void
natTyDescNotUnitTyDesc (Same Refl Refl) impossible

export
natTyNatsNotSame : (contra : n = m -> Void)
                -> (prf    : Equals Universe TYPE (NatTyDesc n) (NatTyDesc m))
                          -> Void
natTyNatsNotSame contra (Same Refl Refl) = contra Refl

export
natTyDescNotFuncDefTyDesc : Equals Universe TYPE (NatTyDesc n) (FuncDefTy u x y) -> Void
natTyDescNotFuncDefTyDesc (Same Refl Refl) impossible

export
natTyDescNotBoolTyDesc : Equals Universe TYPE (NatTyDesc n) BoolTyDesc -> Void
natTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
unitTyDescNotFuncDefTyDesc : Equals Universe TYPE UnitTyDesc (FuncDefTy u x y) -> Void
unitTyDescNotFuncDefTyDesc (Same Refl Refl) impossible

export
unitTyDescNotBoolTyDesc : Equals Universe TYPE UnitTyDesc BoolTyDesc -> Void
unitTyDescNotBoolTyDesc (Same Refl Refl) impossible

export
funcDefTypeParamNotEqual : (contra : Equals Universe TYPE x y -> Void)
                                  -> Equals Universe TYPE (FuncDefTy u x a) (FuncDefTy u y b)
                                  -> Void
funcDefTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcDefTypeReturnNotEqual : (contra : Equals Universe TYPE a b -> Void)
                                   -> Equals Universe TYPE (FuncDefTy u x a) (FuncDefTy u x b)
                                   -> Void
funcDefTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

export
funcDefTypeNotBoolTyDesc : Equals Universe TYPE (FuncDefTy u p r) BoolTyDesc -> Void
funcDefTypeNotBoolTyDesc (Same Refl Refl) impossible


-- [ EOF ]
