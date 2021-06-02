module SystemV.Params.Types.TYPE.Seq

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        SystemV.Params.Types.TYPE

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
             | IsFuncDef
             | IsData
             | IsType
             | IsModule
             | IsChan
             | IsUnit
             | IsPort
             | IsNat
             | IsBool

isData : ValidSeq (DATA _) _ -> Void
isData IsUnit impossible

isType : ValidSeq (IDX TYPE) _ -> Void
isType IsUnit impossible

isFunc : ValidSeq (IDX TERM) (FuncTy _ _) -> Void
isFunc IsUnit impossible

isFuncP : ValidSeq (IDX TERM) (FuncParamTy _ _ _) -> Void
isFuncP IsUnit impossible

isChan : ValidSeq (IDX TERM) (ChanTy) -> Void
isChan IsUnit impossible

isNat : ValidSeq (IDX TERM) (NatTy) -> Void
isNat IsUnit impossible

isBool : ValidSeq (IDX TERM) (BoolTy) -> Void
isBool IsUnit impossible


isPort : ValidSeq (IDX TERM) (PortTy _) -> Void
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

validSeq (IDX TERM) (FuncParamTy _ _ _)
  = No IsFuncDef isFuncP

validSeq (IDX TERM) (ChanTy)
  = No IsChan isChan

validSeq (IDX TERM) (PortTy _)
  = No IsPort isPort

validSeq (IDX TERM) NatTy
  = No IsNat isNat

validSeq (IDX TERM) BoolTy
  = No IsBool isBool

validSeq (IDX TERM) ModuleTy = Yes IsMod
validSeq (IDX TERM) UnitTy = Yes IsUnit


-- [ EOF ]
