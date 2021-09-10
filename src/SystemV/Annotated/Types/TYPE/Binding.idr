module SystemV.Annotated.Types.TYPE.Binding

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.String
import        Data.Maybe

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        SystemV.Annotated.Types.TYPE

%default total

public export
data ValidBind : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    MInst : ValidBind (IDX TERM) ModuleTy
    MDecl : ValidBind (IDX TERM) (FuncTy a b)
    WDecl : ValidBind (IDX TERM) (ChanTy i s type)
    DDecl : ValidBind (DATA TYPE) type

namespace ValidBind

  public export
  data Error = IsType
             | IsUnit
             | IsPort


isDType : ValidBind (DATA TERM) _ -> Void
isDType MDecl impossible

isType : ValidBind (IDX TYPE) _ -> Void
isType MDecl impossible

isPort : ValidBind (IDX TERM) (PortTy _ _ _ _) -> Void
isPort MDecl impossible


isUnit : ValidBind (IDX TERM) UnitTy -> Void
isUnit MDecl impossible


export
validBind : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo ValidBind.Error
                            (ValidBind level type)

validBind (DATA TYPE) type = Yes DDecl

validBind (DATA TERM) _ = No IsType isDType

validBind (IDX TYPE) _ = No IsType isType

validBind (IDX TERM) (FuncTy param return) = Yes MDecl

validBind (IDX TERM) ModuleTy = Yes MInst

validBind (IDX TERM) (ChanTy _ _ _) = Yes WDecl

validBind (IDX TERM) (PortTy _ _ _ _) = No IsPort isPort

validBind (IDX TERM) UnitTy = No IsUnit isUnit


-- [ EOF ]
