module SystemV.Param.Types.TYPE.Function.Argument

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
    IsPortTyDesc : ValidType (IDX TYPE) (PortTyDesc dir)
    IsUnitTyDesc : ValidType (IDX TYPE) UnitTyDesc

namespace ValidType
  public export
  data Error = IsData | IsNat | IsTerm | IsFuncParam | IsFunc | IsModule | IsChan | IsBool

isTyDescData : ValidType (DATA _) type -> Void
isTyDescData IsPortTyDesc impossible

isTyDescTerm : ValidType (IDX TERM) type -> Void
isTyDescTerm IsPortTyDesc impossible

isTyDescFunc : ValidType (IDX TYPE) (FuncTy param return) -> Void
isTyDescFunc IsPortTyDesc impossible

isTyDescFuncParam : ValidType (IDX TYPE) (FuncParamTy u param return) -> Void
isTyDescFuncParam IsPortTyDesc impossible

isTyDescChan : ValidType (IDX TYPE) ChanTyDesc  -> Void
isTyDescChan IsPortTyDesc impossible

isTyDescBool : ValidType (IDX TYPE) BoolTyDesc -> Void
isTyDescBool IsPortTyDesc impossible

isTyDescModule : ValidType (IDX TYPE) ModuleTyDesc -> Void
isTyDescModule IsPortTyDesc impossible

isTyDescNat : ValidType (IDX TYPE) NatTyDesc -> Void
isTyDescNat IsPortTyDesc impossible


export
validType : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Argument.ValidType.Error
                             (ValidType level type)

validType (DATA _) type
  = No IsData isTyDescData
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
  = Yes IsPortTyDesc
validType (IDX TYPE) UnitTyDesc
  = Yes IsUnitTyDesc
validType (IDX TYPE) NatTyDesc
  = No IsNat isTyDescNat


public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsPortTy : ValidTerm (IDX TERM) (PortTy dir)
    IsUnitTy : ValidTerm (IDX TERM) UnitTy

namespace ValidTerm
  public export
  data Error = IsData | IsNat | IsType | IsFunc | IsFuncParam | IsModule | IsChan | IsBool

isTermData : ValidTerm (DATA _) type -> Void
isTermData IsPortTy impossible


isTermType : ValidTerm (IDX TYPE) type -> Void
isTermType IsPortTy impossible


isTermFuncParam : ValidTerm (IDX TERM) (FuncParamTy u param return) -> Void
isTermFuncParam IsPortTy impossible


isTermFunc : ValidTerm (IDX TERM) (FuncTy param return) -> Void
isTermFunc IsPortTy impossible


isTermModule : ValidTerm (IDX TERM) ModuleTy -> Void
isTermModule IsPortTy impossible


isTermBool : ValidTerm (IDX TERM) BoolTy -> Void
isTermBool IsPortTy impossible


isTermChan : ValidTerm (IDX TERM) ChanTy  -> Void
isTermChan IsPortTy impossible

isTermNatTy : ValidTerm (IDX TERM) NatTy -> Void
isTermNatTy IsPortTy impossible

export
validTerm : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Argument.ValidTerm.Error
                             (ValidTerm level type)
validTerm (DATA _) type
  = No IsData isTermData
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

validTerm (IDX TERM) (PortTy dir) = Yes IsPortTy
validTerm (IDX TERM) UnitTy = Yes IsUnitTy
validTerm (IDX TERM) NatTy = No IsNat isTermNatTy

-- [ EOF ]
