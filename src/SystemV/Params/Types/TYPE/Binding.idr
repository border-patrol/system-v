module SystemV.Params.Types.TYPE.Binding

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.String
import        Data.Maybe

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        SystemV.Params.Types.TYPE

%default total

public export
data ValidBind : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    MInst  : ValidBind (IDX TERM) ModuleTy
    MDecl  : ValidBind (IDX TERM) (FuncTy a b)
    MDeclP : ValidBind (IDX TERM) (FuncParamTy u a b)
    WDecl  : ValidBind (IDX TERM) ChanTy
    DDecl  : ValidBind (DATA TERM) type

namespace ValidBind

  public export
  data Error = IsType
             | IsUnit
             | IsPort
             | IsNat
             | IsBool


isDType : ValidBind (DATA TYPE) _ -> Void
isDType MDecl impossible

isType : ValidBind (IDX TYPE) _ -> Void
isType MDecl impossible

isPort : ValidBind (IDX TERM) (PortTy _) -> Void
isPort MDecl impossible

isNat : ValidBind (IDX TERM) NatTy -> Void
isNat MDecl impossible

isBool : ValidBind (IDX TERM) BoolTy -> Void
isBool MDecl impossible

isUnit : ValidBind (IDX TERM) UnitTy -> Void
isUnit MDecl impossible

export
validBind : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo ValidBind.Error
                            (ValidBind level type)

validBind (DATA TERM) type = Yes DDecl

validBind (DATA TYPE) _ = No IsType isDType

validBind (IDX TYPE) _ = No IsType isType

validBind (IDX TERM) (FuncTy param return) = Yes MDecl
validBind (IDX TERM) (FuncParamTy u param return) = Yes MDeclP

validBind (IDX TERM) ModuleTy = Yes MInst

validBind (IDX TERM) ChanTy = Yes WDecl

validBind (IDX TERM) (PortTy _) = No IsPort isPort

validBind (IDX TERM) UnitTy = No IsUnit isUnit
validBind (IDX TERM) BoolTy = No IsBool isBool
validBind (IDX TERM) NatTy = No IsNat isNat


-- [ EOF ]
