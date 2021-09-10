module SystemV.Params.Types.TYPE.Function

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.String
import        Data.Maybe

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed

import        SystemV.Params.Types.TYPE

import public SystemV.Params.Types.TYPE.Function.Argument
import public SystemV.Params.Types.TYPE.Function.Argument.Default
import public SystemV.Params.Types.TYPE.Function.Return
import public SystemV.Params.Types.TYPE.Function.Synthesis

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsValidType : Argument.ValidType (IDX TYPE) param
               -> Return.ValidType   (IDX TYPE) return
               -> ValidType          (IDX TYPE) (FuncTy param return)

    IsValidTypeDef : Argument.Default.ValidType u param
                  -> Return.ValidType           (IDX TYPE) return
                  -> ValidType                  (IDX TYPE) (FuncParamTy u param return)

namespace ValidType

  public export
  data Error = InvalidArgument    Argument.ValidType.Error
             | InvalidArgumentDef Argument.Default.ValidType.Error
             | InvalidReturn      Return.ValidType.Error
             | IsNotFunc
             | IsData
             | IsTerm
             | IsModule
             | IsChan
             | IsUnit
             | IsNat
             | IsPort
             | IsBool
             | IsNotFuncParam

isTyDescData : Function.ValidType (DATA _) type -> Void
isTyDescData (IsValidType x y) impossible

isTyDescTerm : Function.ValidType (IDX TERM) type -> Void
isTyDescTerm (IsValidType x y) impossible

isTyDescNat : Function.ValidType (IDX TYPE) NatTyDesc -> Void
isTyDescNat (IsValidType x y) impossible

isTyDescBool : Function.ValidType (IDX TYPE) BoolTyDesc -> Void
isTyDescBool (IsValidType x y) impossible

isTyDescUnit : Function.ValidType (IDX TYPE) UnitTyDesc -> Void
isTyDescUnit (IsValidType x y) impossible

isTyDescPort : Function.ValidType (IDX TYPE) (PortTyDesc dir) -> Void
isTyDescPort (IsValidType x y) impossible

isTyDescChan : Function.ValidType (IDX TYPE) ChanTyDesc  -> Void
isTyDescChan (IsValidType x y) impossible

isTyDescModule : Function.ValidType (IDX TYPE) ModuleTyDesc -> Void
isTyDescModule (IsValidType x y) impossible

isTyDescInvalidArgument : (Argument.ValidType (IDX TYPE) param -> Void)
                 -> Function.ValidType (IDX TYPE) (FuncTy param return)
                 -> Void
isTyDescInvalidArgument f (IsValidType x y) = f x

isTyDescInvalidReturn : (Return.ValidType (IDX TYPE) return -> Void)
                -> Function.ValidType (IDX TYPE) (FuncTy param return)
                -> Void
isTyDescInvalidReturn f (IsValidType x y) = f y

invalidTypeFuncParam : (Argument.Default.ValidType u param -> Void)
                  -> Function.ValidType (IDX TYPE) (FuncParamTy u param return)
                  -> Void
invalidTypeFuncParam f (IsValidTypeDef x y) = f x

invalidTypeFuncParamRet : (Return.ValidType (IDX TYPE) return -> Void)
                     -> Function.ValidType (IDX TYPE) (FuncParamTy u param return)
                     -> Void
invalidTypeFuncParamRet f (IsValidTypeDef x y) = f y

export
validType : (level : Universe)
           -> (type  : TYPE level)
                     -> DecInfo Function.ValidType.Error
                                (Function.ValidType level type)
validType (DATA _) type
  = No IsData isTyDescData
validType (IDX TERM) type
  = No IsTerm isTyDescTerm

validType (IDX TYPE) ModuleTyDesc
  = No IsModule isTyDescModule
validType (IDX TYPE) ChanTyDesc
  = No IsChan isTyDescChan
validType (IDX TYPE) (PortTyDesc dir)
  = No IsPort isTyDescPort
validType (IDX TYPE) UnitTyDesc
  = No IsUnit isTyDescUnit
validType (IDX TYPE) BoolTyDesc
  = No IsBool isTyDescBool
validType (IDX TYPE) NatTyDesc
  = No IsNat isTyDescNat

validType (IDX TYPE) (FuncTy param return) with (Argument.validType (IDX TYPE) param)
  validType (IDX TYPE) (FuncTy param return) | (Yes prfWhy) with (Return.validType (IDX TYPE) return)
    validType (IDX TYPE) (FuncTy param return) | (Yes prfWhy) | (Yes x)
      = Yes (IsValidType prfWhy x)
    validType (IDX TYPE) (FuncTy param return) | (Yes prfWhy) | (No msgWhyNot prfWhyNot)
      = No (InvalidReturn msgWhyNot) (isTyDescInvalidReturn prfWhyNot)

  validType (IDX TYPE) (FuncTy param return) | (No msgWhyNot prfWhyNot)
    = No (InvalidArgument msgWhyNot) (isTyDescInvalidArgument prfWhyNot)

validType (IDX TYPE) (FuncParamTy u param return) with (Argument.Default.validType u param)
  validType (IDX TYPE) (FuncParamTy u param return) | (Yes prfWhy) with (Return.validType (IDX TYPE) return)
    validType (IDX TYPE) (FuncParamTy u param return) | (Yes prfWhy) | (Yes x)
      = Yes (IsValidTypeDef prfWhy x)

    validType (IDX TYPE) (FuncParamTy u param return) | (Yes prfWhy) | (No msgWhyNot prfWhyNot)
      = No (InvalidReturn msgWhyNot) (invalidTypeFuncParamRet prfWhyNot)

  validType (IDX TYPE) (FuncParamTy u param return) | (No msgWhyNot prfWhyNot)
    = No (InvalidArgumentDef msgWhyNot) (invalidTypeFuncParam prfWhyNot)

public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsValidTerm : Argument.ValidTerm (IDX TERM) param
               -> Return.ValidTerm   (IDX TERM) return
               -> ValidTerm          (IDX TERM) (FuncTy param return)

    IsValidTermDef : Argument.Default.ValidTerm u param
                  -> Return.ValidTerm           (IDX TERM) return
                  -> ValidTerm                  (IDX TERM) (FuncParamTy u param return)

namespace ValidTerm

  public export
  data Error = InvalidArgument    Argument.ValidTerm.Error
             | InvalidArgumentDef Argument.Default.ValidTerm.Error
             | InvalidReturn      Return.ValidTerm.Error
             | IsNotFunc
             | IsData
             | IsType
             | IsModule
             | IsChan
             | IsUnit
             | IsNat
             | IsBool
             | IsPort

isTermData : Function.ValidTerm (DATA _) type -> Void
isTermData (IsValidTerm x y) impossible

isTermType : Function.ValidTerm (IDX TYPE) type -> Void
isTermType (IsValidTerm x y) impossible

isTermNat : Function.ValidTerm (IDX TERM) NatTy -> Void
isTermNat (IsValidTerm x y) impossible

isTermUnit : Function.ValidTerm (IDX TERM) UnitTy -> Void
isTermUnit (IsValidTerm x y) impossible

isTermBool : Function.ValidTerm (IDX TERM) BoolTy -> Void
isTermBool (IsValidTerm x y) impossible

isTermPort : Function.ValidTerm (IDX TERM) (PortTy dir) -> Void
isTermPort (IsValidTerm x y) impossible

isTermChan : Function.ValidTerm (IDX TERM) ChanTy -> Void
isTermChan (IsValidTerm x y) impossible

isTermModule : Function.ValidTerm (IDX TERM) ModuleTy -> Void
isTermModule (IsValidTerm x y) impossible

isTermInvalidArgument : (Argument.ValidTerm (IDX TERM) param -> Void)
                 -> Function.ValidTerm (IDX TERM) (FuncTy param return)
                 -> Void
isTermInvalidArgument f (IsValidTerm x y) = f x

isTermInvalidReturn : (Return.ValidTerm (IDX TERM) return -> Void)
                -> Function.ValidTerm (IDX TERM) (FuncTy param return)
                -> Void
isTermInvalidReturn f (IsValidTerm x y) = f y

invalidTermFuncParam : (Argument.Default.ValidTerm u param -> Void) -> Function.ValidTerm (IDX TERM) (FuncParamTy u param return) -> Void
invalidTermFuncParam f (IsValidTermDef x y) = f x

invalidTermFuncParamRet : (Return.ValidTerm (IDX TERM) return -> Void) -> Function.ValidTerm (IDX TERM) (FuncParamTy u param return) -> Void
invalidTermFuncParamRet f (IsValidTermDef x y) = f y


export
validTerm : (level : Universe)
           -> (type  : TYPE level)
                     -> DecInfo Function.ValidTerm.Error
                                (Function.ValidTerm level type)
validTerm (DATA _) type
  = No IsData isTermData
validTerm (IDX TYPE) type
  = No IsType isTermType

validTerm (IDX TERM) ModuleTy
  = No IsModule isTermModule
validTerm (IDX TERM) ChanTy
  = No IsChan isTermChan
validTerm (IDX TERM) (PortTy dir)
  = No IsPort isTermPort
validTerm (IDX TERM) UnitTy
  = No IsUnit isTermUnit
validTerm (IDX TERM) BoolTy
  = No IsBool isTermBool
validTerm (IDX TERM) NatTy
  = No IsNat isTermNat

validTerm (IDX TERM) (FuncTy param return) with (Argument.validTerm (IDX TERM) param)
  validTerm (IDX TERM) (FuncTy param return) | (Yes prfWhy) with (Return.validTerm (IDX TERM) return)
    validTerm (IDX TERM) (FuncTy param return) | (Yes prfWhy) | (Yes x)
      = Yes (IsValidTerm prfWhy x)
    validTerm (IDX TERM) (FuncTy param return) | (Yes prfWhy) | (No msgWhyNot prfWhyNot)
      = No (InvalidReturn msgWhyNot) (isTermInvalidReturn prfWhyNot)

  validTerm (IDX TERM) (FuncTy param return) | (No msgWhyNot prfWhyNot)
    = No (InvalidArgument msgWhyNot) (isTermInvalidArgument prfWhyNot)

validTerm (IDX TERM) (FuncParamTy u param return) with (Argument.Default.validTerm u param)
  validTerm (IDX TERM) (FuncParamTy u param return) | (Yes prfA) with (Return.validTerm (IDX TERM) return)
    validTerm (IDX TERM) (FuncParamTy u param return) | (Yes prfA) | (Yes prfR)
      = Yes (IsValidTermDef prfA prfR)
    validTerm (IDX TERM) (FuncParamTy u param return) | (Yes prfA) | (No msgWhyNot prfWhyNot)
      = No (InvalidReturn msgWhyNot) (invalidTermFuncParamRet prfWhyNot)

  validTerm (IDX TERM) (FuncParamTy u param return) | (No msgWhyNot prfWhyNot)
    = No (InvalidArgumentDef msgWhyNot) (invalidTermFuncParam prfWhyNot)


-- [ EOF ]
