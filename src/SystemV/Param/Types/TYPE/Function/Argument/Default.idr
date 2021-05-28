module SystemV.Param.Types.TYPE.Function.Argument.Default

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Param.Types.TYPE

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsNatTyDesc  : ValidType (IDX  TYPE) NatTyDesc
    IsDataType   : ValidType (DATA TYPE) DATATYPE

namespace ValidType
  public export
  data Error = IsDataTerm | IsTerm | IsFuncParam | IsFunc | IsModule | IsChan | IsBool | IsPort | IsUnit | IsData

isTyDescData : ValidType (DATA TERM) type -> Void
isTyDescData IsNatTyDesc impossible


isTyDescTerm : ValidType (IDX TERM) type -> Void
isTyDescTerm IsNatTyDesc impossible

isTyDescFunc : ValidType (IDX TYPE) (FuncTy param return) -> Void
isTyDescFunc IsNatTyDesc impossible


isTyDescFuncParam : ValidType (IDX TYPE) (FuncParamTy u param return) -> Void
isTyDescFuncParam IsNatTyDesc impossible


isTyDescChan : ValidType (IDX TYPE) ChanTyDesc  -> Void
isTyDescChan IsNatTyDesc impossible

isTyDescBool : ValidType (IDX TYPE) BoolTyDesc -> Void
isTyDescBool IsNatTyDesc impossible

isTyDescModule : ValidType (IDX TYPE) ModuleTyDesc -> Void
isTyDescModule IsNatTyDesc impossible


isPortTyDesc : ValidType (IDX TYPE) (PortTyDesc dir) -> Void
isPortTyDesc IsNatTyDesc impossible

isUnitTyDesc : ValidType (IDX TYPE) UnitTyDesc -> Void
isUnitTyDesc IsNatTyDesc impossible


export
validType : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Argument.Default.ValidType.Error
                             (ValidType level type)

validType (DATA TYPE) DATATYPE  = Yes IsDataType
validType (DATA TERM) type
  = No IsDataTerm isTyDescData

validType (IDX TERM) type
  = No IsTerm isTyDescTerm
validType (IDX TYPE) (FuncTy param return)
  = No IsFunc isTyDescFunc
validType (IDX TYPE) (FuncParamTy u param return)
  = No IsFuncParam isTyDescFuncParam
validType (IDX TYPE) ModuleTyDesc
  = No IsModule isTyDescModule
validType (IDX TYPE) ChanTyDesc
  = No IsChan isTyDescChan
validType (IDX TYPE) BoolTyDesc
  = No IsBool isTyDescBool

validType (IDX TYPE) (PortTyDesc dir)
  = No IsPort isPortTyDesc

validType (IDX TYPE) UnitTyDesc
  = No IsUnit isUnitTyDesc


validType (IDX TYPE) NatTyDesc
  = Yes IsNatTyDesc


public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsNatTy  : ValidTerm (IDX TERM)  NatTy
    IsDataTy : ValidTerm (DATA TERM)  type

namespace ValidTerm
  public export
  data Error = IsData | IsType | IsFunc | IsFuncParam | IsModule | IsChan | IsBool | IsPort | IsUnit

isTermDataType : ValidTerm (DATA TYPE) type -> Void
isTermDataType IsNatTy impossible

isTermType : ValidTerm (IDX TYPE) type -> Void
isTermType IsNatTy impossible

isTermFuncParam : ValidTerm (IDX TERM) (FuncParamTy u param return) -> Void
isTermFuncParam IsNatTy impossible

isTermFunc : ValidTerm (IDX TERM) (FuncTy param return) -> Void
isTermFunc IsNatTy impossible

isTermModule : ValidTerm (IDX TERM) ModuleTy -> Void
isTermModule IsNatTy impossible

isTermBool : ValidTerm (IDX TERM) BoolTy -> Void
isTermBool IsNatTy impossible


isTermChan : ValidTerm (IDX TERM) ChanTy  -> Void
isTermChan IsNatTy impossible


isTermPort : ValidTerm (IDX TERM) (PortTy dir) -> Void
isTermPort IsNatTy impossible


isTermUnit : ValidTerm (IDX TERM) UnitTy -> Void
isTermUnit IsNatTy impossible


export
validTerm : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Argument.Default.ValidTerm.Error
                             (ValidTerm level type)
validTerm (DATA TERM) type = Yes IsDataTy
validTerm (DATA TYPE) type
  = No IsData isTermDataType

validTerm (IDX TYPE) type
  = No IsType isTermType

validTerm (IDX TERM) (FuncTy param return)
  = No IsFunc isTermFunc
validTerm (IDX TERM) (FuncParamTy u param return)
  = No IsFuncParam isTermFuncParam
validTerm (IDX TERM) ModuleTy
  = No IsModule isTermModule
validTerm (IDX TERM) ChanTy
  = No IsChan isTermChan
validTerm (IDX TERM) BoolTy
  = No IsBool isTermBool

validTerm (IDX TERM) (PortTy dir)
  = No IsPort isTermPort

validTerm (IDX TERM) UnitTy
  = No IsUnit isTermUnit

validTerm (IDX TERM) NatTy = Yes IsNatTy

-- [ EOF ]
