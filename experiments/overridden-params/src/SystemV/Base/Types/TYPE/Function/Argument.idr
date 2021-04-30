module SystemV.Base.Types.TYPE.Function.Argument

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Base.Types.TYPE

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsPortTyDesc : ValidType (IDX TYPE) (PortTyDesc type dir)
    IsUnitTyDesc : ValidType (IDX TYPE) UnitTyDesc
    IsNatTyDesc  : ValidType (IDX TYPE) (NatTyDesc n)

namespace ValidType
  public export
  data Error = IsData | IsTerm | IsFunc | IsModule | IsChan

isTyDescData : ValidType (DATA _) type -> Void
isTyDescData IsPortTyDesc impossible
isTyDescData IsUnitTyDesc impossible
isTyDescData IsNatTyDesc impossible

isTyDescTerm : ValidType (IDX TERM) type -> Void
isTyDescTerm IsPortTyDesc impossible
isTyDescTerm IsUnitTyDesc impossible
isTyDescTerm IsNatTyDesc impossible

isTyDescFunc : ValidType (IDX TYPE) (FuncTy param return) -> Void
isTyDescFunc IsPortTyDesc impossible
isTyDescFunc IsUnitTyDesc impossible
isTyDescFunc IsNatTyDesc impossible

isTyDescChan : ValidType (IDX TYPE) (ChanTyDesc type) -> Void
isTyDescChan IsPortTyDesc impossible
isTyDescChan IsUnitTyDesc impossible
isTyDescChan IsNatTyDesc impossible

isTyDescModule : ValidType (IDX TYPE) ModuleTyDesc -> Void
isTyDescModule IsPortTyDesc impossible
isTyDescModule IsUnitTyDesc impossible
isTyDescModule IsNatTyDesc impossible

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
validType (IDX TYPE) (ChanTyDesc type)
  = No IsChan isTyDescChan

validType (IDX TYPE) (PortTyDesc type dir)
  = Yes IsPortTyDesc
validType (IDX TYPE) UnitTyDesc
  = Yes IsUnitTyDesc
validType (IDX TYPE) (NatTyDesc k)
  = Yes IsNatTyDesc


public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsPortTy : ValidTerm (IDX TERM) (PortTy type dir)
    IsUnitTy : ValidTerm (IDX TERM) UnitTy
    IsNatTy  : ValidTerm (IDX TERM) (NatTy n)

namespace ValidTerm
  public export
  data Error = IsData | IsType | IsFunc | IsModule | IsChan

isTermData : ValidTerm (DATA _) type -> Void
isTermData IsPortTy impossible
isTermData IsUnitTy impossible
isTermData IsNatTy impossible

isTermType : ValidTerm (IDX TYPE) type -> Void
isTermType IsPortTy impossible
isTermType IsUnitTy impossible
isTermType IsNatTy impossible

isTermFunc : ValidTerm (IDX TERM) (FuncTy param return) -> Void
isTermFunc IsPortTy impossible
isTermFunc IsUnitTy impossible
isTermFunc IsNatTy impossible

isTermModule : ValidTerm (IDX TERM) ModuleTy -> Void
isTermModule IsPortTy impossible
isTermModule IsUnitTy impossible
isTermModule IsNatTy impossible

isTermChan : ValidTerm (IDX TERM) (ChanTy type) -> Void
isTermChan IsPortTy impossible
isTermChan IsUnitTy impossible
isTermChan IsNatTy impossible


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
validTerm (IDX TERM) (ChanTy type)
  = No IsChan isTermChan

validTerm (IDX TERM) (PortTy type dir) = Yes IsPortTy
validTerm (IDX TERM) UnitTy = Yes IsUnitTy
validTerm (IDX TERM) (NatTy k) = Yes IsNatTy

-- [ EOF ]
