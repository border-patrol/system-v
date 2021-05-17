module SystemV.Annotated.Types.TYPE.Function.Argument

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Annotated.Types.TYPE

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsPortTyDesc : ValidType (IDX TYPE) (PortTyDesc type dir sense intent)
    IsUnitTyDesc : ValidType (IDX TYPE) UnitTyDesc

namespace ValidType
  public export
  data Error = IsData | IsTerm | IsFunc | IsModule | IsChan

isTyDescData : ValidType (DATA _) type -> Void
isTyDescData IsPortTyDesc impossible
isTyDescData IsUnitTyDesc impossible


isTyDescTerm : ValidType (IDX TERM) type -> Void
isTyDescTerm IsPortTyDesc impossible
isTyDescTerm IsUnitTyDesc impossible


isTyDescFunc : ValidType (IDX TYPE) (FuncTy param return) -> Void
isTyDescFunc IsPortTyDesc impossible
isTyDescFunc IsUnitTyDesc impossible


isTyDescChan : ValidType (IDX TYPE) (ChanTyDesc type sense intent) -> Void
isTyDescChan IsPortTyDesc impossible
isTyDescChan IsUnitTyDesc impossible


isTyDescModule : ValidType (IDX TYPE) ModuleTyDesc -> Void
isTyDescModule IsPortTyDesc impossible
isTyDescModule IsUnitTyDesc impossible


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
validType (IDX TYPE) ModuleTyDesc
  = No IsModule isTyDescModule
validType (IDX TYPE) (ChanTyDesc type sense intent)
  = No IsChan isTyDescChan

validType (IDX TYPE) (PortTyDesc type dir sense intent)
  = Yes IsPortTyDesc
validType (IDX TYPE) UnitTyDesc
  = Yes IsUnitTyDesc

public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsPortTy : ValidTerm (IDX TERM) (PortTy type dir sense intent)
    IsUnitTy : ValidTerm (IDX TERM) UnitTy

namespace ValidTerm
  public export
  data Error = IsData | IsType | IsFunc | IsModule | IsChan

isTermData : ValidTerm (DATA _) type -> Void
isTermData IsPortTy impossible
isTermData IsUnitTy impossible

isTermType : ValidTerm (IDX TYPE) type -> Void
isTermType IsPortTy impossible
isTermType IsUnitTy impossible

isTermFunc : ValidTerm (IDX TERM) (FuncTy param return) -> Void
isTermFunc IsPortTy impossible
isTermFunc IsUnitTy impossible

isTermModule : ValidTerm (IDX TERM) ModuleTy -> Void
isTermModule IsPortTy impossible
isTermModule IsUnitTy impossible

isTermChan : ValidTerm (IDX TERM) (ChanTy type sense intent) -> Void
isTermChan IsPortTy impossible
isTermChan IsUnitTy impossible


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
validTerm (IDX TERM) ModuleTy
  = No IsModule isTermModule
validTerm (IDX TERM) (ChanTy type sense intent)
  = No IsChan isTermChan

validTerm (IDX TERM) (PortTy type dir sense intent) = Yes IsPortTy
validTerm (IDX TERM) UnitTy = Yes IsUnitTy

-- [ EOF ]
