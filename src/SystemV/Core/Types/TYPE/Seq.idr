module SystemV.Core.Types.TYPE.Seq

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.String
import        Data.Maybe

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        SystemV.Core.Types.TYPE

%default total

public export
data ValidSeq : (level : Universe)
             -> (type  : TYPE level)
                      -> Type
  where
    IsUnit : ValidSeq (IDX TERM) UnitTy
    IsMod  : ValidSeq (IDX TERM) ModuleTy

namespace ValidSeq

  public export
  data Error = IsFunc
             | IsData
             | IsType
             | IsModule
             | IsChan
             | IsUnit
             | IsPort


isData : ValidSeq (DATA _) _ -> Void
isData IsUnit impossible

isType : ValidSeq (IDX TYPE) _ -> Void
isType IsUnit impossible

isFunc : ValidSeq (IDX TERM) (FuncTy _ _) -> Void
isFunc IsUnit impossible

isChan : ValidSeq (IDX TERM) (ChanTy _) -> Void
isChan IsUnit impossible

isPort : ValidSeq (IDX TERM) (PortTy _ _) -> Void
isPort IsUnit impossible

export
validSeq : (level : Universe)
        -> (type  : TYPE level)
                 -> DecInfo ValidSeq.Error
                            (ValidSeq level type)
validSeq (DATA _) _
  = No IsData isData

validSeq (IDX TYPE) _
  = No IsType isType

validSeq (IDX TERM) (FuncTy _ _)
  = No IsFunc isFunc

validSeq (IDX TERM) (ChanTy _)
  = No IsChan isChan

validSeq (IDX TERM) (PortTy _ _)
  = No IsPort isPort

validSeq (IDX TERM) ModuleTy = Yes IsMod
validSeq (IDX TERM) UnitTy = Yes IsUnit


-- [ EOF ]
