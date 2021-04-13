module SystemV.Types.TYPE.Function.Return

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import SystemV.Utilities

import SystemV.Types.TYPE

%default total

public export
data ValidType : (level : Universe)
                  -> (type  : TYPE level)
                           -> Type
  where
    IsModuleTyDesc : ValidType (IDX TYPE) ModuleTyDesc
    IsUnitTyDesc   : ValidType (IDX TYPE) UnitTyDesc

    IsFuncTyDesc : ValidType (IDX TYPE) return
          -> ValidType (IDX TYPE) (FuncTy param return)

namespace ValidType
  public export
  data Error = IsData | IsTerm | IsChan | IsPort | IsNat | IsErrFunc Return.ValidType.Error

isTyDescData : ValidType (DATA _) type -> Void
isTyDescData IsModuleTyDesc impossible
isTyDescData IsUnitTyDesc impossible
isTyDescData (IsFuncTyDesc x) impossible

isTyDescTerm : ValidType (IDX TERM) type -> Void
isTyDescTerm IsModuleTyDesc impossible
isTyDescTerm IsUnitTyDesc impossible
isTyDescTerm (IsFuncTyDesc x) impossible

isTyDescChan : ValidType (IDX TYPE) (ChanTyDesc type) -> Void
isTyDescChan IsModuleTyDesc impossible
isTyDescChan IsUnitTyDesc impossible
isTyDescChan (IsFuncTyDesc x) impossible

isTyDescPort : ValidType (IDX TYPE) (PortTyDesc type dir) -> Void
isTyDescPort IsModuleTyDesc impossible
isTyDescPort IsUnitTyDesc impossible
isTyDescPort (IsFuncTyDesc x) impossible

isTyDescNat : ValidType (IDX TYPE) (NatTyDesc k) -> Void
isTyDescNat IsModuleTyDesc impossible
isTyDescNat IsUnitTyDesc impossible
isTyDescNat (IsFuncTyDesc x) impossible

isTyDescFunc : (ValidType (IDX TYPE) return -> Void)
      -> ValidType (IDX TYPE) (FuncTy param return)
      -> Void
isTyDescFunc f (IsFuncTyDesc x) = f x

export
validType : (level : Universe)
             -> (type  : TYPE level)
                      -> DecInfo Return.ValidType.Error
                                 (ValidType level type)
validType (DATA _) type = No IsData isTyDescData
validType (IDX TERM) type = No IsTerm isTyDescTerm

validType (IDX TYPE) (ChanTyDesc type) = No IsChan isTyDescChan
validType (IDX TYPE) (PortTyDesc type dir) = No IsPort isTyDescPort
validType (IDX TYPE) (NatTyDesc k) = No IsNat isTyDescNat

validType (IDX TYPE) UnitTyDesc = Yes IsUnitTyDesc
validType (IDX TYPE) ModuleTyDesc = Yes IsModuleTyDesc
validType (IDX TYPE) (FuncTy param return) with (validType (IDX TYPE) return)
  validType (IDX TYPE) (FuncTy param return) | (Yes prfWhy) = Yes (IsFuncTyDesc prfWhy)
  validType (IDX TYPE) (FuncTy param return) | (No msgWhyNot prfWhyNot) = No (IsErrFunc msgWhyNot) (isTyDescFunc prfWhyNot)

public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsModuleTy : ValidTerm (IDX TERM) ModuleTy
    IsUnitTy   : ValidTerm (IDX TERM) UnitTy

    IsFuncTy : ValidTerm (IDX TERM) return
          -> ValidTerm (IDX TERM) (FuncTy param return)

namespace ValidTerm
  public export
  data Error = IsData | IsTerm | IsChan | IsPort | IsNat | IsErrFunc Return.ValidTerm.Error

isTermData : ValidTerm (DATA _) type -> Void
isTermData IsModuleTy impossible
isTermData IsUnitTy impossible
isTermData (IsFuncTy x) impossible

isTermTerm : ValidTerm (IDX TYPE) type -> Void
isTermTerm IsModuleTy impossible
isTermTerm IsUnitTy impossible
isTermTerm (IsFuncTy x) impossible

isTermChan : ValidTerm (IDX TERM) (ChanTy type) -> Void
isTermChan IsModuleTy impossible
isTermChan IsUnitTy impossible
isTermChan (IsFuncTy x) impossible

isTermPort : ValidTerm (IDX TERM) (PortTy type dir) -> Void
isTermPort IsModuleTy impossible
isTermPort IsUnitTy impossible
isTermPort (IsFuncTy x) impossible

isTermNat : ValidTerm (IDX TERM) (NatTy k) -> Void
isTermNat IsModuleTy impossible
isTermNat IsUnitTy impossible
isTermNat (IsFuncTy x) impossible

isTermFunc : (ValidTerm (IDX TERM) return -> Void)
      -> ValidTerm (IDX TERM) (FuncTy param return)
      -> Void
isTermFunc f (IsFuncTy x) = f x

export
validTerm : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Return.ValidTerm.Error
                             (ValidTerm level type)
validTerm (DATA _) type = No IsData isTermData
validTerm (IDX TYPE) type = No IsTerm isTermTerm

validTerm (IDX TERM) (ChanTy type) = No IsChan isTermChan
validTerm (IDX TERM) (PortTy type dir) = No IsPort isTermPort
validTerm (IDX TERM) (NatTy k) = No IsNat isTermNat

validTerm (IDX TERM) UnitTy = Yes IsUnitTy
validTerm (IDX TERM) ModuleTy = Yes IsModuleTy
validTerm (IDX TERM) (FuncTy param return) with (validTerm (IDX TERM) return)
  validTerm (IDX TERM) (FuncTy param return) | (Yes prfWhy) = Yes (IsFuncTy prfWhy)
  validTerm (IDX TERM) (FuncTy param return) | (No msgWhyNot prfWhyNot) = No (IsErrFunc msgWhyNot) (isTermFunc prfWhyNot)


-- [ EOF ]
