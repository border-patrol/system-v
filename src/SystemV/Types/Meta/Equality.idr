module SystemV.Types.Meta.Equality

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Utilities
import SystemV.Types.Direction
import SystemV.Types.Meta

%default total

public export
data Error = KindMismatch Universe Universe
           | TypeMismatch (Meta a) (Meta a)


namespace DataTypeTypes
  typeDefTyTypeNotEqual : (contra : Equals Universe Meta x y -> Void)
                       -> (prf    : Equals Universe Meta (TypeDefTy x) (TypeDefTy y))
                                 -> Void
  typeDefTyTypeNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

  typeDefTyTypeNotABool : Equals Universe Meta (TypeDefTy x) BoolTyDesc -> Void
  typeDefTyTypeNotABool (Same Refl Refl) impossible

  typeDefTyTypeNotALogic : Equals Universe Meta (TypeDefTy x) LogicTyDesc -> Void
  typeDefTyTypeNotALogic (Same Refl Refl) impossible

  typeDefTyTypeNotAVect : Equals Universe Meta (TypeDefTy x) (VectorTyDesc n y) -> Void
  typeDefTyTypeNotAVect (Same Refl Refl) impossible

  boolTypeNotALogic : Equals Universe Meta BoolTyDesc LogicTyDesc -> Void
  boolTypeNotALogic (Same Refl Refl) impossible

  boolTypeNotAVect : Equals Universe Meta BoolTyDesc (VectorTyDesc n x) -> Void
  boolTypeNotAVect (Same Refl Refl) impossible

  logicTypeNotAVect : Equals Universe Meta LogicTyDesc (VectorTyDesc n x) -> Void
  logicTypeNotAVect (Same Refl Refl) impossible

  vectTypeDiffSize : (contra : Not (n === m))
                  -> (prf    : Equals Universe Meta (VectorTyDesc n x) (VectorTyDesc m y))
                            -> Void
  vectTypeDiffSize contra (Same Refl Refl) = contra Refl

  vectTypeDiffType : (contra : Not (Equals Universe Meta x y))
                  -> (prf    : Equals Universe Meta (VectorTyDesc n x) (VectorTyDesc n y))
                            -> Void
  vectTypeDiffType contra (Same Refl Refl) = contra (Same Refl Refl)

  export
  decEqTypesDataTypes : (a,b : Meta (DATA TYPE))
                            -> DecInfo Error (Equals Universe Meta a b)
  decEqTypesDataTypes a b with (a)
    decEqTypesDataTypes a b | (TypeDefTy x) with (b)
      decEqTypesDataTypes a b | (TypeDefTy x) | (TypeDefTy y) with (decEqTypesDataTypes x y)
        decEqTypesDataTypes a b | (TypeDefTy x) | (TypeDefTy y) | (Yes prf) with (prf)
          decEqTypesDataTypes a b | (TypeDefTy x) | (TypeDefTy x) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
        decEqTypesDataTypes a b | (TypeDefTy x) | (TypeDefTy y) | (No msg contra) =  No  msg (typeDefTyTypeNotEqual contra)

      decEqTypesDataTypes a b | (TypeDefTy x) | BoolTyDesc =  No (TypeMismatch a b) (typeDefTyTypeNotABool)

      decEqTypesDataTypes a b | (TypeDefTy x) | LogicTyDesc =  No (TypeMismatch a b) (typeDefTyTypeNotALogic)

      decEqTypesDataTypes a b | (TypeDefTy x) | (VectorTyDesc n y) =  No (TypeMismatch a b) (typeDefTyTypeNotAVect)

    decEqTypesDataTypes a b | BoolTyDesc with (b)
      decEqTypesDataTypes a b | BoolTyDesc | (TypeDefTy x) =  No (TypeMismatch a b) (negEqSym typeDefTyTypeNotABool)

      decEqTypesDataTypes a b | BoolTyDesc | BoolTyDesc = Yes (Same Refl Refl)
      decEqTypesDataTypes a b | BoolTyDesc | LogicTyDesc =  No (TypeMismatch a b) (boolTypeNotALogic)
      decEqTypesDataTypes a b | BoolTyDesc | (VectorTyDesc n x) =  No (TypeMismatch a b) (boolTypeNotAVect)

    decEqTypesDataTypes a b | LogicTyDesc with (b)
      decEqTypesDataTypes a b | LogicTyDesc | (TypeDefTy x) =  No (TypeMismatch a b) (negEqSym typeDefTyTypeNotALogic)
      decEqTypesDataTypes a b | LogicTyDesc | BoolTyDesc =  No (TypeMismatch a b) (negEqSym boolTypeNotALogic)
      decEqTypesDataTypes a b | LogicTyDesc | LogicTyDesc = Yes (Same Refl Refl)
      decEqTypesDataTypes a b | LogicTyDesc | (VectorTyDesc n x) =  No (TypeMismatch a b) logicTypeNotAVect

    decEqTypesDataTypes a b | (VectorTyDesc n x) with (b)
      decEqTypesDataTypes a b | (VectorTyDesc n x) | (TypeDefTy y) =  No (TypeMismatch a b) (negEqSym typeDefTyTypeNotAVect)
      decEqTypesDataTypes a b | (VectorTyDesc n x) | BoolTyDesc =  No (TypeMismatch a b) (negEqSym boolTypeNotAVect)
      decEqTypesDataTypes a b | (VectorTyDesc n x) | LogicTyDesc =  No (TypeMismatch a b) (negEqSym logicTypeNotAVect)
      decEqTypesDataTypes a b | (VectorTyDesc n x) | (VectorTyDesc k y) with (decEq n k)
        decEqTypesDataTypes a b | (VectorTyDesc k x) | (VectorTyDesc k y) | (Yes Refl) with (decEqTypesDataTypes x y)
          decEqTypesDataTypes a b | (VectorTyDesc k x) | (VectorTyDesc k y) | (Yes Refl) | (Yes prfWhy) with (prfWhy)
            decEqTypesDataTypes a b | (VectorTyDesc k y) | (VectorTyDesc k y) | (Yes Refl) | (Yes prfWhy) | (Same Refl Refl)
              = Yes (Same Refl Refl)

          decEqTypesDataTypes a b | (VectorTyDesc k x) | (VectorTyDesc k y) | (Yes Refl) | (No msgWhyNot prfWhyNot)
            = No msgWhyNot (vectTypeDiffType prfWhyNot)

        decEqTypesDataTypes a b | (VectorTyDesc n x) | (VectorTyDesc k y) | (No contra)
          = No (TypeMismatch a b) (vectTypeDiffSize contra)

namespace DataTypeValues
  typeDefTyValueNotEqual : (contra : Equals Universe Meta x y -> Void)
                       -> (prf    : Equals Universe Meta (TypeDefTy x) (TypeDefTy y))
                                 -> Void
  typeDefTyValueNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

  typeDefTyValueNotABool : Equals Universe Meta (TypeDefTy x) BoolTy -> Void
  typeDefTyValueNotABool (Same Refl Refl) impossible

  typeDefTyValueNotALogic : Equals Universe Meta (TypeDefTy x) LogicTy -> Void
  typeDefTyValueNotALogic (Same Refl Refl) impossible

  typeDefTyValueNotAVect : Equals Universe Meta (TypeDefTy x) (VectorTy n y) -> Void
  typeDefTyValueNotAVect (Same Refl Refl) impossible

  boolTypeNotALogic : Equals Universe Meta BoolTy LogicTy -> Void
  boolTypeNotALogic (Same Refl Refl) impossible

  boolTypeNotAVect : Equals Universe Meta BoolTy (VectorTy n x) -> Void
  boolTypeNotAVect (Same Refl Refl) impossible

  logicTypeNotAVect : Equals Universe Meta LogicTy (VectorTy n x) -> Void
  logicTypeNotAVect (Same Refl Refl) impossible

  vectTypeDiffSize : (contra : Not (n === m))
                  -> (prf    : Equals Universe Meta (VectorTy n x) (VectorTy m y))
                            -> Void
  vectTypeDiffSize contra (Same Refl Refl) = contra Refl

  vectTypeDiffType : (contra : Not (Equals Universe Meta x y))
                  -> (prf    : Equals Universe Meta (VectorTy n x) (VectorTy n y))
                            -> Void
  vectTypeDiffType contra (Same Refl Refl) = contra (Same Refl Refl)

  export
  decEqTypesDataValues : (a,b : Meta (DATA VALUE))
                            -> DecInfo Error (Equals Universe Meta a b)
  decEqTypesDataValues a b with (a)
    decEqTypesDataValues a b | (TypeDefTy x) with (b)
      decEqTypesDataValues a b | (TypeDefTy x) | (TypeDefTy y) with (decEqTypesDataValues x y)
        decEqTypesDataValues a b | (TypeDefTy x) | (TypeDefTy y) | (Yes prf) with (prf)
          decEqTypesDataValues a b | (TypeDefTy x) | (TypeDefTy x) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
        decEqTypesDataValues a b | (TypeDefTy x) | (TypeDefTy y) | (No msg contra) =  No msg (typeDefTyValueNotEqual contra)

      decEqTypesDataValues a b | (TypeDefTy x) | BoolTy =  No (TypeMismatch a b) (typeDefTyValueNotABool)

      decEqTypesDataValues a b | (TypeDefTy x) | LogicTy =  No (TypeMismatch a b) (typeDefTyValueNotALogic)

      decEqTypesDataValues a b | (TypeDefTy x) | (VectorTy n y) =  No (TypeMismatch a b) (typeDefTyValueNotAVect)

    decEqTypesDataValues a b | BoolTy with (b)
      decEqTypesDataValues a b | BoolTy | (TypeDefTy x) =  No (TypeMismatch a b) (negEqSym typeDefTyValueNotABool)

      decEqTypesDataValues a b | BoolTy | BoolTy = Yes (Same Refl Refl)
      decEqTypesDataValues a b | BoolTy | LogicTy =  No (TypeMismatch a b) (boolTypeNotALogic)
      decEqTypesDataValues a b | BoolTy | (VectorTy n x) =  No (TypeMismatch a b) (boolTypeNotAVect)

    decEqTypesDataValues a b | LogicTy with (b)
      decEqTypesDataValues a b | LogicTy | (TypeDefTy x) =  No (TypeMismatch a b) (negEqSym typeDefTyValueNotALogic)
      decEqTypesDataValues a b | LogicTy | BoolTy =  No (TypeMismatch a b) (negEqSym boolTypeNotALogic)
      decEqTypesDataValues a b | LogicTy | LogicTy = Yes (Same Refl Refl)
      decEqTypesDataValues a b | LogicTy | (VectorTy n x) =  No (TypeMismatch a b) logicTypeNotAVect

    decEqTypesDataValues a b | (VectorTy n x) with (b)
      decEqTypesDataValues a b | (VectorTy n x) | (TypeDefTy y) =  No (TypeMismatch a b) (negEqSym typeDefTyValueNotAVect)
      decEqTypesDataValues a b | (VectorTy n x) | BoolTy =  No (TypeMismatch a b) (negEqSym boolTypeNotAVect)
      decEqTypesDataValues a b | (VectorTy n x) | LogicTy =  No (TypeMismatch a b) (negEqSym logicTypeNotAVect)
      decEqTypesDataValues a b | (VectorTy n x) | (VectorTy k y) with (decEq n k)
        decEqTypesDataValues a b | (VectorTy k x) | (VectorTy k y) | (Yes Refl) with (decEqTypesDataValues x y)
          decEqTypesDataValues a b | (VectorTy k x) | (VectorTy k y) | (Yes Refl) | (Yes prf) with (prf)
            decEqTypesDataValues a b | (VectorTy k y) | (VectorTy k y) | (Yes Refl) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
          decEqTypesDataValues a b | (VectorTy k x) | (VectorTy k y) | (Yes Refl) | (No msg contra) =  No msg (vectTypeDiffType contra)
        decEqTypesDataValues a b | (VectorTy n x) | (VectorTy k y) | (No contra) =  No (TypeMismatch a b) (vectTypeDiffSize contra)

namespace TypeTypes

  funcTypeTyDescNotModuleTyDesc : (Equals Universe Meta (FuncTy x y) ModuleTyDesc)
                               -> Void
  funcTypeTyDescNotModuleTyDesc (Same Refl Refl) impossible

  funcTypeTyDescNotChanTyDesc : (Equals Universe Meta (FuncTy x y) (ChanTy t))
                             -> Void
  funcTypeTyDescNotChanTyDesc (Same Refl Refl) impossible

  funcTypeTyDescNotPortTyDesc : (Equals Universe Meta (FuncTy x y) (PortTy t d))
                             -> Void
  funcTypeTyDescNotPortTyDesc (Same Refl Refl) impossible

  funcTypeTyDescNotParamTyDesc : (Equals Universe Meta (FuncTy x y) (ParamTy))
                              -> Void
  funcTypeTyDescNotParamTyDesc (Same Refl Refl) impossible

  funcTypeTyDescNotUnitTyDesc : (Equals Universe Meta (FuncTy x y) UnitTy)
                             -> Void
  funcTypeTyDescNotUnitTyDesc (Same Refl Refl) impossible

  funcTypeParamNotEqual : (contra : Equals Universe Meta x y -> Void)
                                 -> Equals Universe Meta (FuncTy x a) (FuncTy y b)
                                 -> Void
  funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

  funcTypeReturnNotEqual : (contra : Equals Universe Meta a b -> Void)
                                  -> Equals Universe Meta (FuncTy x a) (FuncTy x b)
                                  -> Void
  funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

  moduleTyDescNotChanTyDesc : Equals Universe Meta (ModuleTyDesc) (ChanTy type) -> Void
  moduleTyDescNotChanTyDesc (Same Refl Refl) impossible

  moduleTyDescNotPortTyDesc : Equals Universe Meta (ModuleTyDesc) (PortTy type dir) -> Void
  moduleTyDescNotPortTyDesc (Same Refl Refl) impossible

  moduleTyDescNotParamTyDesc : Equals Universe Meta (ModuleTyDesc) ParamTy -> Void
  moduleTyDescNotParamTyDesc (Same Refl Refl) impossible

  moduleTyDescNotUnitTyDesc : Equals Universe Meta (ModuleTyDesc) UnitTy -> Void
  moduleTyDescNotUnitTyDesc (Same Refl Refl) impossible

  chanTyDescNotPortTyDesc : Equals Universe Meta (ChanTy type) (PortTy t d) -> Void
  chanTyDescNotPortTyDesc (Same Refl Refl) impossible

  chanTyDescNotParamTyDesc : Equals Universe Meta (ChanTy type) ParamTy -> Void
  chanTyDescNotParamTyDesc (Same Refl Refl) impossible

  chanTyDescNotUnitTyDesc : Equals Universe Meta (ChanTy type) UnitTy -> Void
  chanTyDescNotUnitTyDesc (Same Refl Refl) impossible

  chanTyDescDiffTypes : (contra : Equals Universe Meta x y -> Void)
                     -> (prf    : Equals Universe Meta (ChanTy x) (ChanTy y))
                               -> Void
  chanTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

  portTyDescNotParamTyDesc : Equals Universe Meta (PortTy type dir) ParamTy -> Void
  portTyDescNotParamTyDesc (Same Refl Refl) impossible

  portTyDescNotUnitTyDesc : Equals Universe Meta (PortTy type dir) UnitTy -> Void
  portTyDescNotUnitTyDesc (Same Refl Refl) impossible

  portTyDescDiffTypes : (contra : Equals Universe Meta x y -> Void)
                     -> (prf    : Equals Universe Meta (PortTy x a) (PortTy y b))
                               -> Void
  portTyDescDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

  portTyDescDiffDirs : (contra : a === b -> Void)
                    -> (prf    : Equals Universe Meta (PortTy x a) (PortTy x b))
                              -> Void
  portTyDescDiffDirs contra (Same Refl Refl) = contra Refl

  paramTyDescNotUnitTyDesc : Equals Universe Meta ParamTy UnitTy -> Void
  paramTyDescNotUnitTyDesc (Same Refl Refl) impossible


  export
  decEqTypeTypes : (a,b : Meta (IDX TYPE))
                        -> DecInfo Error (Equals Universe Meta a b)
  decEqTypeTypes a b with (a)
    decEqTypeTypes a b | (FuncTy x y) with (b)
      decEqTypeTypes a b | (FuncTy x y) | (FuncTy z w) with (decEqTypeTypes x z)
        decEqTypeTypes a b | (FuncTy x y) | (FuncTy z w) | (Yes prf) with (prf)
          decEqTypeTypes a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) with (decEqTypeTypes y w)
            decEqTypeTypes a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) | (Yes z) with (z)
              decEqTypeTypes a b | (FuncTy x y) | (FuncTy x y) | (Yes prf) | (Same Refl Refl) | (Yes z) | (Same Refl Refl)
                = Yes (Same Refl Refl)
            decEqTypeTypes a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) | (No msg contra)
              =  No msg (funcTypeReturnNotEqual contra)
        decEqTypeTypes a b | (FuncTy x y) | (FuncTy z w) | (No msg contra)
          =  No msg (funcTypeParamNotEqual contra)

      decEqTypeTypes a b | (FuncTy x y) | ModuleTyDesc =  No (TypeMismatch a b) (funcTypeTyDescNotModuleTyDesc)
      decEqTypeTypes a b | (FuncTy x y) | (ChanTy type) =  No (TypeMismatch a b) (funcTypeTyDescNotChanTyDesc)
      decEqTypeTypes a b | (FuncTy x y) | (PortTy type dir) =  No (TypeMismatch a b) (funcTypeTyDescNotPortTyDesc)
      decEqTypeTypes a b | (FuncTy x y) | ParamTy =  No (TypeMismatch a b) (funcTypeTyDescNotParamTyDesc)
      decEqTypeTypes a b | (FuncTy x y) | UnitTy =  No (TypeMismatch a b) (funcTypeTyDescNotUnitTyDesc)

    decEqTypeTypes a b | ModuleTyDesc with (b)
      decEqTypeTypes a b | ModuleTyDesc | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyDescNotModuleTyDesc)
      decEqTypeTypes a b | ModuleTyDesc | ModuleTyDesc = Yes (Same Refl Refl)
      decEqTypeTypes a b | ModuleTyDesc | (ChanTy type) =  No (TypeMismatch a b) moduleTyDescNotChanTyDesc
      decEqTypeTypes a b | ModuleTyDesc | (PortTy type dir) =  No (TypeMismatch a b) moduleTyDescNotPortTyDesc
      decEqTypeTypes a b | ModuleTyDesc | ParamTy =  No (TypeMismatch a b) moduleTyDescNotParamTyDesc
      decEqTypeTypes a b | ModuleTyDesc | UnitTy =  No (TypeMismatch a b) moduleTyDescNotUnitTyDesc

    decEqTypeTypes a b | (ChanTy type) with (b)
      decEqTypeTypes a b | (ChanTy type) | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyDescNotChanTyDesc)
      decEqTypeTypes a b | (ChanTy type) | ModuleTyDesc =  No (TypeMismatch a b) (negEqSym moduleTyDescNotChanTyDesc)
      decEqTypeTypes a b | (ChanTy type) | (ChanTy x) with (decEqTypesDataTypes type x)
        decEqTypeTypes a b | (ChanTy type) | (ChanTy x) | (Yes prf) with (prf)
          decEqTypeTypes a b | (ChanTy type) | (ChanTy type) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
        decEqTypeTypes a b | (ChanTy type) | (ChanTy x) | (No msg contra) =  No msg (chanTyDescDiffTypes contra)
      decEqTypeTypes a b | (ChanTy type) | (PortTy x dir) =  No (TypeMismatch a b) chanTyDescNotPortTyDesc
      decEqTypeTypes a b | (ChanTy type) | ParamTy =  No (TypeMismatch a b) chanTyDescNotParamTyDesc
      decEqTypeTypes a b | (ChanTy type) | UnitTy =  No (TypeMismatch a b) chanTyDescNotUnitTyDesc

    decEqTypeTypes a b | (PortTy type dir) with (b)
      decEqTypeTypes a b | (PortTy type dir) | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyDescNotPortTyDesc)
      decEqTypeTypes a b | (PortTy type dir) | ModuleTyDesc =  No (TypeMismatch a b) (negEqSym moduleTyDescNotPortTyDesc)
      decEqTypeTypes a b | (PortTy type dir) | (ChanTy x) =  No (TypeMismatch a b) (negEqSym chanTyDescNotPortTyDesc)
      decEqTypeTypes a b | (PortTy type dir) | (PortTy x y) with (decEqTypesDataTypes type x)
        decEqTypeTypes a b | (PortTy type dir) | (PortTy x y) | (Yes prf) with (prf)
          decEqTypeTypes a b | (PortTy type dir) | (PortTy type y) | (Yes prf) | (Same Refl Refl) with (Direction.Equality.decEq dir y)
            decEqTypeTypes a b | (PortTy type y) | (PortTy type y) | (Yes prf) | (Same Refl Refl) | (Yes Refl)
              = Yes (Same Refl Refl)
            decEqTypeTypes a b | (PortTy type dir) | (PortTy type y) | (Yes prf) | (Same Refl Refl) | (No contra)
              =  No (TypeMismatch a b) (portTyDescDiffDirs contra)
        decEqTypeTypes a b | (PortTy type dir) | (PortTy x y) | (No msg contra) =  No msg (portTyDescDiffTypes contra)
      decEqTypeTypes a b | (PortTy type dir) | ParamTy =  No (TypeMismatch a b) portTyDescNotParamTyDesc
      decEqTypeTypes a b | (PortTy type dir) | UnitTy =  No (TypeMismatch a b) portTyDescNotUnitTyDesc

    decEqTypeTypes a b | ParamTy with (b)
      decEqTypeTypes a b | ParamTy | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyDescNotParamTyDesc)
      decEqTypeTypes a b | ParamTy | ModuleTyDesc =  No (TypeMismatch a b) (negEqSym moduleTyDescNotParamTyDesc)
      decEqTypeTypes a b | ParamTy | (ChanTy type) =  No (TypeMismatch a b) (negEqSym chanTyDescNotParamTyDesc)
      decEqTypeTypes a b | ParamTy | (PortTy type dir) =  No (TypeMismatch a b) (negEqSym portTyDescNotParamTyDesc)
      decEqTypeTypes a b | ParamTy | ParamTy = Yes (Same Refl Refl)
      decEqTypeTypes a b | ParamTy | UnitTy =  No (TypeMismatch a b) paramTyDescNotUnitTyDesc

    decEqTypeTypes a b | UnitTy with (b)
      decEqTypeTypes a b | UnitTy | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyDescNotUnitTyDesc)
      decEqTypeTypes a b | UnitTy | ModuleTyDesc =  No (TypeMismatch a b) (negEqSym moduleTyDescNotUnitTyDesc)
      decEqTypeTypes a b | UnitTy | (ChanTy type) =  No (TypeMismatch a b) (negEqSym chanTyDescNotUnitTyDesc)
      decEqTypeTypes a b | UnitTy | (PortTy type dir) =  No (TypeMismatch a b) (negEqSym portTyDescNotUnitTyDesc)
      decEqTypeTypes a b | UnitTy | ParamTy =  No (TypeMismatch a b) (negEqSym paramTyDescNotUnitTyDesc)
      decEqTypeTypes a b | UnitTy | UnitTy = Yes (Same Refl Refl)

namespace TypeValues

  funcTypeTyValNotModuleTyVal : (Equals Universe Meta (FuncTy x y) ModuleVal)
                               -> Void
  funcTypeTyValNotModuleTyVal (Same Refl Refl) impossible

  funcTypeTyValNotChanTyVal : (Equals Universe Meta (FuncTy x y) (ChanVal t))
                             -> Void
  funcTypeTyValNotChanTyVal (Same Refl Refl) impossible

  funcTypeTyValNotPortTyVal : (Equals Universe Meta (FuncTy x y) (PortVal t d))
                             -> Void
  funcTypeTyValNotPortTyVal (Same Refl Refl) impossible

  funcTypeTyValNotParamTyVal : (Equals Universe Meta (FuncTy x y) (ParamVal))
                              -> Void
  funcTypeTyValNotParamTyVal (Same Refl Refl) impossible

  funcTypeTyValNotUnitTyVal : (Equals Universe Meta (FuncTy x y) UnitVal)
                             -> Void
  funcTypeTyValNotUnitTyVal (Same Refl Refl) impossible

  funcTypeParamNotEqual : (contra : Equals Universe Meta x y -> Void)
                                 -> Equals Universe Meta (FuncTy x a) (FuncTy y b)
                                 -> Void
  funcTypeParamNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

  funcTypeReturnNotEqual : (contra : Equals Universe Meta a b -> Void)
                                  -> Equals Universe Meta (FuncTy x a) (FuncTy x b)
                                  -> Void
  funcTypeReturnNotEqual contra (Same Refl Refl) = contra (Same Refl Refl)

  moduleTyValNotChanTyVal : Equals Universe Meta (ModuleVal) (ChanVal type) -> Void
  moduleTyValNotChanTyVal (Same Refl Refl) impossible

  moduleTyValNotPortTyVal : Equals Universe Meta (ModuleVal) (PortVal type dir) -> Void
  moduleTyValNotPortTyVal (Same Refl Refl) impossible

  moduleTyValNotParamTyVal : Equals Universe Meta (ModuleVal) ParamVal -> Void
  moduleTyValNotParamTyVal (Same Refl Refl) impossible

  moduleTyValNotUnitTyVal : Equals Universe Meta (ModuleVal) UnitVal -> Void
  moduleTyValNotUnitTyVal (Same Refl Refl) impossible

  chanTyValNotPortTyVal : Equals Universe Meta (ChanVal type) (PortVal t d) -> Void
  chanTyValNotPortTyVal (Same Refl Refl) impossible

  chanTyValNotParamTyVal : Equals Universe Meta (ChanVal type) ParamVal -> Void
  chanTyValNotParamTyVal (Same Refl Refl) impossible

  chanTyValNotUnitTyVal : Equals Universe Meta (ChanVal type) UnitVal -> Void
  chanTyValNotUnitTyVal (Same Refl Refl) impossible

  chanTyValDiffTypes : (contra : Equals Universe Meta x y -> Void)
                     -> (prf    : Equals Universe Meta (ChanVal x) (ChanVal y))
                               -> Void
  chanTyValDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

  portTyValNotParamTyVal : Equals Universe Meta (PortVal type dir) ParamVal -> Void
  portTyValNotParamTyVal (Same Refl Refl) impossible

  portTyValNotUnitTyVal : Equals Universe Meta (PortVal type dir) UnitVal -> Void
  portTyValNotUnitTyVal (Same Refl Refl) impossible

  portTyValDiffTypes : (contra : Equals Universe Meta x y -> Void)
                     -> (prf    : Equals Universe Meta (PortVal x a) (PortVal y b))
                               -> Void
  portTyValDiffTypes contra (Same Refl Refl) = contra (Same Refl Refl)

  portTyValDiffDirs : (contra : a === b -> Void)
                    -> (prf   : Equals Universe Meta (PortVal type a) (PortVal x b))
                             -> Void
  portTyValDiffDirs contra (Same Refl Refl) = contra Refl

  paramTyValNotUnitTyVal : Equals Universe Meta ParamVal UnitVal -> Void
  paramTyValNotUnitTyVal (Same Refl Refl) impossible


  export
  decEqTypeValues : (a,b : Meta (IDX VALUE))
                        -> DecInfo Error (Equals Universe Meta a b)
  decEqTypeValues a b with (a)
    decEqTypeValues a b | (FuncTy x y) with (b)
      decEqTypeValues a b | (FuncTy x y) | (FuncTy z w) with (decEqTypeValues x z)
        decEqTypeValues a b | (FuncTy x y) | (FuncTy z w) | (Yes prf) with (prf)
          decEqTypeValues a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) with (decEqTypeValues y w)
            decEqTypeValues a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) | (Yes z) with (z)
              decEqTypeValues a b | (FuncTy x y) | (FuncTy x y) | (Yes prf) | (Same Refl Refl) | (Yes z) | (Same Refl Refl)
                = Yes (Same Refl Refl)
            decEqTypeValues a b | (FuncTy x y) | (FuncTy x w) | (Yes prf) | (Same Refl Refl) | (No msg contra)
              = No msg (funcTypeReturnNotEqual contra)
        decEqTypeValues a b | (FuncTy x y) | (FuncTy z w) | (No msg contra)
          =  No msg (funcTypeParamNotEqual contra)

      decEqTypeValues a b | (FuncTy x y) | ModuleVal =  No (TypeMismatch a b) (funcTypeTyValNotModuleTyVal)
      decEqTypeValues a b | (FuncTy x y) | (ChanVal type) =  No (TypeMismatch a b) (funcTypeTyValNotChanTyVal)
      decEqTypeValues a b | (FuncTy x y) | (PortVal type dir) =  No (TypeMismatch a b) (funcTypeTyValNotPortTyVal)
      decEqTypeValues a b | (FuncTy x y) | ParamVal =  No (TypeMismatch a b) (funcTypeTyValNotParamTyVal)
      decEqTypeValues a b | (FuncTy x y) | UnitVal =  No (TypeMismatch a b) (funcTypeTyValNotUnitTyVal)

    decEqTypeValues a b | ModuleVal with (b)
      decEqTypeValues a b | ModuleVal | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyValNotModuleTyVal)
      decEqTypeValues a b | ModuleVal | ModuleVal = Yes (Same Refl Refl)
      decEqTypeValues a b | ModuleVal | (ChanVal type) =  No (TypeMismatch a b) moduleTyValNotChanTyVal
      decEqTypeValues a b | ModuleVal | (PortVal type dir) =  No (TypeMismatch a b) moduleTyValNotPortTyVal
      decEqTypeValues a b | ModuleVal | ParamVal =  No (TypeMismatch a b) moduleTyValNotParamTyVal
      decEqTypeValues a b | ModuleVal | UnitVal =  No (TypeMismatch a b) moduleTyValNotUnitTyVal

    decEqTypeValues a b | (ChanVal type) with (b)
      decEqTypeValues a b | (ChanVal type) | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyValNotChanTyVal)
      decEqTypeValues a b | (ChanVal type) | ModuleVal =  No (TypeMismatch a b) (negEqSym moduleTyValNotChanTyVal)
      decEqTypeValues a b | (ChanVal type) | (ChanVal x) with (decEqTypesDataTypes type x)
        decEqTypeValues a b | (ChanVal type) | (ChanVal x) | (Yes prf) with (prf)
          decEqTypeValues a b | (ChanVal type) | (ChanVal type) | (Yes prf) | (Same Refl Refl) = Yes (Same Refl Refl)
        decEqTypeValues a b | (ChanVal type) | (ChanVal x) | (No msg contra) =  No msg (chanTyValDiffTypes contra)
      decEqTypeValues a b | (ChanVal type) | (PortVal x dir) =  No (TypeMismatch a b) chanTyValNotPortTyVal
      decEqTypeValues a b | (ChanVal type) | ParamVal =  No (TypeMismatch a b) chanTyValNotParamTyVal
      decEqTypeValues a b | (ChanVal type) | UnitVal =  No (TypeMismatch a b) chanTyValNotUnitTyVal

    decEqTypeValues a b | (PortVal type dir) with (b)
      decEqTypeValues a b | (PortVal type dir) | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyValNotPortTyVal)
      decEqTypeValues a b | (PortVal type dir) | ModuleVal =  No (TypeMismatch a b) (negEqSym moduleTyValNotPortTyVal)
      decEqTypeValues a b | (PortVal type dir) | (ChanVal x) =  No (TypeMismatch a b) (negEqSym chanTyValNotPortTyVal)
      decEqTypeValues a b | (PortVal type dir) | (PortVal x y) with (decEqTypesDataTypes type x)
        decEqTypeValues a b | (PortVal type dir) | (PortVal x y) | (Yes prf) with (prf)
          decEqTypeValues a b | (PortVal type dir) | (PortVal type y) | (Yes prf) | (Same Refl Refl) with (Direction.Equality.decEq dir y)
            decEqTypeValues a b | (PortVal type y) | (PortVal type y) | (Yes prf) | (Same Refl Refl) | (Yes Refl)
              = Yes (Same Refl Refl)
            decEqTypeValues a b | (PortVal type dir) | (PortVal type y) | (Yes prf) | (Same Refl Refl) | (No contra)
              =  No (TypeMismatch a b) (portTyValDiffDirs contra)
        decEqTypeValues a b | (PortVal type dir) | (PortVal x y) | (No msg contra) =  No msg  (portTyValDiffTypes contra)
      decEqTypeValues a b | (PortVal type dir) | ParamVal =  No (TypeMismatch a b) portTyValNotParamTyVal
      decEqTypeValues a b | (PortVal type dir) | UnitVal =  No (TypeMismatch a b) portTyValNotUnitTyVal

    decEqTypeValues a b | ParamVal with (b)
      decEqTypeValues a b | ParamVal | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyValNotParamTyVal)
      decEqTypeValues a b | ParamVal | ModuleVal =  No (TypeMismatch a b) (negEqSym moduleTyValNotParamTyVal)
      decEqTypeValues a b | ParamVal | (ChanVal type) =  No (TypeMismatch a b) (negEqSym chanTyValNotParamTyVal)
      decEqTypeValues a b | ParamVal | (PortVal type dir) =  No (TypeMismatch a b) (negEqSym portTyValNotParamTyVal)
      decEqTypeValues a b | ParamVal | ParamVal = Yes (Same Refl Refl)
      decEqTypeValues a b | ParamVal | UnitVal =  No (TypeMismatch a b) paramTyValNotUnitTyVal

    decEqTypeValues a b | UnitVal with (b)
      decEqTypeValues a b | UnitVal | (FuncTy x y) =  No (TypeMismatch a b) (negEqSym funcTypeTyValNotUnitTyVal)
      decEqTypeValues a b | UnitVal | ModuleVal =  No (TypeMismatch a b) (negEqSym moduleTyValNotUnitTyVal)
      decEqTypeValues a b | UnitVal | (ChanVal type) =  No (TypeMismatch a b) (negEqSym chanTyValNotUnitTyVal)
      decEqTypeValues a b | UnitVal | (PortVal type dir) =  No (TypeMismatch a b) (negEqSym portTyValNotUnitTyVal)
      decEqTypeValues a b | UnitVal | ParamVal =  No (TypeMismatch a b) (negEqSym paramTyValNotUnitTyVal)
      decEqTypeValues a b | UnitVal | UnitVal = Yes (Same Refl Refl)


data ByIndex : {idxA,idxB : Universe}
            -> (a   : Meta idxA)
            -> (b   : Meta idxB)
                   -> Type
  where
    IdxSame : {idxA,idxB  : Universe}
           -> (a          : Meta idxA)
           -> (b          : Meta idxB)
           -> (prf        : idxA === idxB)
                         -> ByIndex a b

    IdxDiff : {idxA, idxB : Universe}
           -> (a : Meta idxA)
           -> (b : Meta idxB)
           -> (prf : Not (idxA === idxB))
                  -> ByIndex a b

byIndex : {idxA, idxB : Universe}
       -> (a : Meta idxA)
       -> (b : Meta idxB)
       -> ByIndex a b
byIndex a b {idxA} {idxB} with (decEq idxA idxB)
  byIndex a b {idxA = idxB} {idxB = idxB} | (Yes Refl) = (IdxSame a b Refl)
  byIndex a b {idxA = idxA} {idxB = idxB} | (No contra) = (IdxDiff a b contra)

export
decEqTypes : {aidx,bidx : Universe}
          -> (a         : Meta aidx)
          -> (b         : Meta bidx)
                       -> DecInfo Error (Equals Universe Meta a b)
decEqTypes a b {aidx} {bidx} with (byIndex a b)
  decEqTypes a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) with (bidx)
    decEqTypes a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (DATA VALUE)
      = decEqTypesDataValues a b
    decEqTypes a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (DATA TYPE)
      = decEqTypesDataTypes a b
    decEqTypes a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (IDX VALUE)
      = decEqTypeValues a b
    decEqTypes a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (IDX TYPE)
      = decEqTypeTypes a b
  decEqTypes a b {aidx = aidx} {bidx = bidx} | (IdxDiff a b contra)
    = No (KindMismatch aidx bidx) (indexAreSame contra)


-- --------------------------------------------------------------------- [ EOF ]
