module SystemV.DSL.Build.Helpers

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

import        SystemV.Types
import        SystemV.Terms

import        SystemV.DSL.AST
import        SystemV.Utilities

%default total

namespace FuncParam

  namespace Type
    public export
    data ValidFuncParam : (level : Universe)
                       -> (type  : Meta level) -> Type where
      IsPort  : ValidFuncParam (IDX TYPE) (PortTy x dir)
      IsParam : ValidFuncParam (IDX TYPE) ParamTy
      IsUnit  : ValidFuncParam (IDX TYPE) UnitTy


    isDataType : ValidFuncParam (DATA TYPE) type -> Void
    isDataType IsPort impossible
    isDataType IsParam impossible
    isDataType IsUnit impossible

    isDataValue : ValidFuncParam (DATA VALUE) type -> Void
    isDataValue IsPort impossible
    isDataValue IsParam impossible
    isDataValue IsUnit impossible

    isIdxValue : ValidFuncParam (IDX VALUE) type -> Void
    isIdxValue IsPort impossible
    isIdxValue IsParam impossible
    isIdxValue IsUnit impossible

    isModule  : ValidFuncParam (IDX TYPE) ModuleTyDesc -> Void
    isModule IsPort impossible
    isModule IsParam impossible
    isModule IsUnit impossible

    isFunc  : ValidFuncParam (IDX TYPE) (FuncTy x y) -> Void
    isFunc IsPort impossible
    isFunc IsParam impossible
    isFunc IsUnit impossible

    isChan  : ValidFuncParam (IDX TYPE) (ChanTy t) -> Void
    isChan IsPort impossible
    isChan IsParam impossible
    isChan IsUnit impossible

    export
    validFuncParam : (level : Universe)
                  -> (type  : Meta level)
                  -> Dec (ValidFuncParam level type)
    validFuncParam (IDX TYPE) (FuncTy x y) = No isFunc
    validFuncParam (IDX TYPE) ModuleTyDesc = No isModule
    validFuncParam (IDX TYPE) (ChanTy type) = No isChan
    validFuncParam (IDX TYPE) (PortTy type dir) = Yes IsPort
    validFuncParam (IDX TYPE) ParamTy = Yes IsParam
    validFuncParam (IDX TYPE) UnitTy = Yes IsUnit

    validFuncParam (IDX VALUE) type = No isIdxValue
    validFuncParam (DATA VALUE) type = No isDataValue
    validFuncParam (DATA TYPE) type = No isDataType

  namespace Value

    public export
    data ValidFuncParamValue : (level : Universe)
                            -> (type  : Meta level)
                            -> (value : Meta (IDX VALUE))
                                     -> Type where
       VFPV : ValidFuncParam (IDX TYPE) type -> (value : Meta (IDX VALUE)) -> ValidFuncParamValue (IDX TYPE) type value

    isNotValidFPV : (contra : ValidFuncParam level type -> Void)
                 -> (prf    : (value ** ValidFuncParamValue level type value))
                           -> Void
    isNotValidFPV contra (MkDPair fst (VFPV x fst)) = contra x

    export
    validFuncParamValue : (level : Universe)
                       -> (type  : Meta level)
                                -> Dec (value ** ValidFuncParamValue level type value)
    validFuncParamValue level type with (validFuncParam level type)
      validFuncParamValue (IDX TYPE) (PortTy x dir) | (Yes IsPort)
        = Yes (_ ** VFPV IsPort (PortVal x dir))
      validFuncParamValue (IDX TYPE) ParamTy | (Yes IsParam)
        = Yes (_ ** VFPV IsParam ParamVal)
      validFuncParamValue (IDX TYPE) UnitTy | (Yes IsUnit)
        = Yes (_ ** VFPV IsUnit UnitVal)
      validFuncParamValue level type | (No contra)
        = No (isNotValidFPV contra)

  namespace Valid

    public export
    data ValidFuncTy : (level : Universe)
                    -> (type  : Meta level)
                             -> Type
      where
        IsValid  : ValidFuncParamValue (IDX TYPE) type value
                -> TyCheck type value
                -> ValidFuncTy (IDX TYPE) type
        IsValidNot : ValidFuncTy (IDX TYPE) rest
        IsNotAType : ValidFuncTy level type

    export
    isFuncTy : (level : Universe) -> (type : Meta level) -> ValidFuncTy level type
    isFuncTy (IDX TYPE) type with (validFuncParamValue (IDX TYPE) type)
      isFuncTy (IDX TYPE) type | (Yes (value ** VFPV x value)) with (typeCheck type value)
        isFuncTy (IDX TYPE) type | (Yes (value ** VFPV x value)) | (Yes prfWhy) = IsValid (VFPV x value) prfWhy

        isFuncTy (IDX TYPE) type | (Yes (value ** VFPV x value)) | (No msgWhyNot prfWhyNot) = IsValidNot -- really an internal error
      isFuncTy (IDX TYPE) type | (No contra) = IsValidNot
    isFuncTy _ _ = IsNotAType
