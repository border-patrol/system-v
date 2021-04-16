module SystemV.Params.Types.TYPE.Function.Argument.Default

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Params.Types.TYPE

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsNatTyDesc  : ValidType (IDX  TYPE) (NatTyDesc n)
    IsData       : ValidType (DATA TYPE) type

namespace ValidType
  public export
  data Error = IsDataTerm | IsTerm | IsFuncDef | IsFunc | IsModule | IsChan | IsBool | IsPort | IsUnit

isTyDescData : ValidType (DATA TERM) type -> Void
isTyDescData IsNatTyDesc impossible
isTyDescData IsData impossible

isTyDescTerm : ValidType (IDX TERM) type -> Void
isTyDescTerm IsNatTyDesc impossible
isTyDescTerm IsData impossible

isTyDescFunc : ValidType (IDX TYPE) (FuncTy param return) -> Void
isTyDescFunc IsNatTyDesc impossible
isTyDescFunc IsData impossible

isTyDescFuncDef : ValidType (IDX TYPE) (FuncDefTy u param return) -> Void
isTyDescFuncDef IsNatTyDesc impossible
isTyDescFuncDef IsData impossible

isTyDescChan : ValidType (IDX TYPE) (ChanTyDesc type) -> Void
isTyDescChan IsNatTyDesc impossible
isTyDescChan IsData impossible

isTyDescBool : ValidType (IDX TYPE) BoolTyDesc -> Void
isTyDescBool IsNatTyDesc impossible
isTyDescBool IsData impossible

isTyDescModule : ValidType (IDX TYPE) ModuleTyDesc -> Void
isTyDescModule IsNatTyDesc impossible
isTyDescModule IsData impossible

isPortTyDesc : ValidType (IDX TYPE) (PortTyDesc type dir) -> Void
isPortTyDesc IsNatTyDesc impossible
isPortTyDesc IsData impossible

isTyDescDataTerm : ValidType (DATA TERM) type -> Void
isTyDescDataTerm IsNatTyDesc impossible
isTyDescDataTerm IsData impossible

isUnitTyDesc : ValidType (IDX TYPE) UnitTyDesc -> Void
isUnitTyDesc IsNatTyDesc impossible
isUnitTyDesc IsData impossible

export
validType : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Argument.Default.ValidType.Error
                             (ValidType level type)

validType (DATA TERM) type
  = No IsDataTerm isTyDescDataTerm

validType (DATA TYPE) type
  = Yes IsData

validType (IDX TERM) type
  = No IsTerm isTyDescTerm
validType (IDX TYPE) (FuncTy param return)
  = No IsFunc isTyDescFunc
validType (IDX TYPE) (FuncDefTy u param return)
  = No IsFuncDef isTyDescFuncDef
validType (IDX TYPE) ModuleTyDesc
  = No IsModule isTyDescModule
validType (IDX TYPE) (ChanTyDesc type)
  = No IsChan isTyDescChan
validType (IDX TYPE) BoolTyDesc
  = No IsBool isTyDescBool

validType (IDX TYPE) (PortTyDesc type dir)
  = No IsPort isPortTyDesc

validType (IDX TYPE) UnitTyDesc
  = No IsUnit isUnitTyDesc


validType (IDX TYPE) (NatTyDesc k)
  = Yes IsNatTyDesc


public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsNatTy  : ValidTerm (IDX TERM)  (NatTy n)
    IsDataTy : ValidTerm (DATA TYPE) type

namespace ValidTerm
  public export
  data Error = IsData | IsType | IsFunc | IsFuncDef | IsModule | IsChan | IsBool | IsPort | IsUnit

isTermData : ValidTerm (DATA TERM) type -> Void
isTermData IsNatTy impossible
isTermData IsDataTy impossible

isTermType : ValidTerm (IDX TYPE) type -> Void
isTermType IsNatTy impossible
isTermType IsDataTy impossible

isTermFuncDef : ValidTerm (IDX TERM) (FuncDefTy u param return) -> Void
isTermFuncDef IsNatTy impossible
isTermFuncDef IsDataTy impossible

isTermFunc : ValidTerm (IDX TERM) (FuncTy param return) -> Void
isTermFunc IsNatTy impossible
isTermFunc IsDataTy impossible

isTermModule : ValidTerm (IDX TERM) ModuleTy -> Void
isTermModule IsNatTy impossible
isTermModule IsDataTy impossible

isTermBool : ValidTerm (IDX TERM) BoolTy -> Void
isTermBool IsNatTy impossible
isTermBool IsDataTy impossible

isTermChan : ValidTerm (IDX TERM) (ChanTy type) -> Void
isTermChan IsNatTy impossible
isTermChan IsDataTy impossible

isTermPort : ValidTerm (IDX TERM) (PortTy type dir) -> Void
isTermPort IsNatTy impossible
isTermPort IsDataTy impossible

isTermUnit : ValidTerm (IDX TERM) UnitTy -> Void
isTermUnit IsNatTy impossible
isTermUnit IsDataTy impossible

export
validTerm : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Argument.Default.ValidTerm.Error
                             (ValidTerm level type)
validTerm (DATA TERM) type
  = No IsData isTermData

validTerm (DATA TYPE) type
  = Yes IsDataTy

validTerm (IDX TYPE) type
  = No IsType isTermType

validTerm (IDX TERM) (FuncTy param return)
  = No IsFunc isTermFunc
validTerm (IDX TERM) (FuncDefTy u param return)
  = No IsFuncDef isTermFuncDef
validTerm (IDX TERM) ModuleTy
  = No IsModule isTermModule
validTerm (IDX TERM) (ChanTy type)
  = No IsChan isTermChan
validTerm (IDX TERM) BoolTy
  = No IsBool isTermBool

validTerm (IDX TERM) (PortTy type dir)
  = No IsPort isTermPort

validTerm (IDX TERM) UnitTy
  = No IsUnit isTermUnit

validTerm (IDX TERM) (NatTy k) = Yes IsNatTy

-- [ EOF ]
