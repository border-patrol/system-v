module SystemV.Param.Types.TYPE.Function.Return

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Param.Types.TYPE

import SystemV.Param.Types.TYPE.Function.Argument
import SystemV.Param.Types.TYPE.Function.Argument.Default

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsModuleTyDesc : Return.ValidType (IDX TYPE) ModuleTyDesc
    IsUnitTyDesc   : Return.ValidType (IDX TYPE) UnitTyDesc

    IsFuncParamTyDesc : Argument.Default.ValidType u param
                   -> Return.ValidType (IDX TYPE) return
                   -> Return.ValidType (IDX TYPE) (FuncParamTy u param return)

    IsFuncTyDesc : Argument.ValidType (IDX TYPE) param
                -> Return.ValidType (IDX TYPE) return
                -> Return.ValidType (IDX TYPE) (FuncTy param return)

namespace ValidType
  public export
  data Error = IsData | IsTerm | IsChan | IsPort | IsNat | IsBool
             | IsErrFunc  Return.ValidType.Error
             | IsErrFuncP Argument.ValidType.Error
             | IsErrFuncQ Argument.Default.ValidType.Error

isTyDescData : Return.ValidType (DATA _) type -> Void
isTyDescData IsModuleTyDesc impossible

isTyDescTerm : Return.ValidType (IDX TERM) type -> Void
isTyDescTerm IsModuleTyDesc impossible


isTyDescChan : Return.ValidType (IDX TYPE) ChanTyDesc -> Void
isTyDescChan IsModuleTyDesc impossible

isTyDescBool : Return.ValidType (IDX TYPE) BoolTyDesc -> Void
isTyDescBool IsModuleTyDesc impossible


isTyDescPort : Return.ValidType (IDX TYPE) (PortTyDesc dir) -> Void
isTyDescPort IsModuleTyDesc impossible


isTyDescNat : Return.ValidType (IDX TYPE) NatTyDesc -> Void
isTyDescNat IsModuleTyDesc impossible

isTyDescFuncParam : (Return.ValidType (IDX TYPE) return -> Void)
               -> Return.ValidType (IDX TYPE) (FuncParamTy u param return)
               -> Void
isTyDescFuncParam f (IsFuncParamTyDesc p x) = f x

isTyDescFuncParamP : (Argument.Default.ValidType u param -> Void)
                -> Return.ValidType (IDX TYPE) (FuncParamTy u param return)
                -> Void
isTyDescFuncParamP f (IsFuncParamTyDesc x y) = f x

isTyDescFunc : (Return.ValidType (IDX TYPE) return -> Void)
      -> Return.ValidType (IDX TYPE) (FuncTy param return)
      -> Void
isTyDescFunc f (IsFuncTyDesc p x) = f x

isTyDescFuncP : (Argument.ValidType (IDX TYPE) param -> Void)
             -> Return.ValidType (IDX TYPE) (FuncTy param return)
             -> Void
isTyDescFuncP f (IsFuncTyDesc x y) = f x


export
validType : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Return.ValidType.Error
                            (Return.ValidType level type)
validType (DATA _) type = No IsData isTyDescData
validType (IDX TERM) type = No IsTerm isTyDescTerm

validType (IDX TYPE) ChanTyDesc = No IsChan isTyDescChan
validType (IDX TYPE) (PortTyDesc dir) = No IsPort isTyDescPort
validType (IDX TYPE) NatTyDesc = No IsNat isTyDescNat
validType (IDX TYPE) BoolTyDesc = No IsNat isTyDescBool

validType (IDX TYPE) UnitTyDesc = Yes IsUnitTyDesc
validType (IDX TYPE) ModuleTyDesc = Yes IsModuleTyDesc

validType (IDX TYPE) (FuncTy param return) with (Argument.validType (IDX TYPE) param)
  validType (IDX TYPE) (FuncTy param return) | (Yes prfP) with (Return.validType (IDX TYPE) return)
    validType (IDX TYPE) (FuncTy param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncTyDesc prfP prfR)

    validType (IDX TYPE) (FuncTy param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTyDescFunc prfWhyNot)

  validType (IDX TYPE) (FuncTy param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncP msgWhyNot) (isTyDescFuncP prfWhyNot)

validType (IDX TYPE) (FuncParamTy u param return) with (Argument.Default.validType u param)
  validType (IDX TYPE) (FuncParamTy u param return) | (Yes prfP) with (Return.validType (IDX TYPE) return)
    validType (IDX TYPE) (FuncParamTy u param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncParamTyDesc prfP prfR)

    validType (IDX TYPE) (FuncParamTy u param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTyDescFuncParam prfWhyNot)

  validType (IDX TYPE) (FuncParamTy u param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncQ msgWhyNot) (isTyDescFuncParamP prfWhyNot)

public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsModuleTy : Return.ValidTerm (IDX TERM) ModuleTy
    IsUnitTy   : Return.ValidTerm (IDX TERM) UnitTy

    IsFuncParamTy : Argument.Default.ValidTerm u param
               -> Return.ValidTerm (IDX TERM) return
               -> Return.ValidTerm (IDX TERM) (FuncParamTy u param return)

    IsFuncTy : Argument.ValidTerm (IDX TERM) param
            -> Return.ValidTerm (IDX TERM) return
            -> Return.ValidTerm (IDX TERM) (FuncTy param return)


namespace ValidTerm
  public export
  data Error = IsData | IsTerm | IsChan | IsPort | IsBool | IsNat
             | IsErrFunc Return.ValidTerm.Error
             | IsErrFuncP Argument.ValidTerm.Error
             | IsErrFuncQ Argument.Default.ValidTerm.Error

isTermData : Return.ValidTerm (DATA _) type -> Void
isTermData IsModuleTy impossible


isTermTerm : Return.ValidTerm (IDX TYPE) type -> Void
isTermTerm IsModuleTy impossible

isTermChan : Return.ValidTerm (IDX TERM) ChanTy -> Void
isTermChan IsModuleTy impossible

isTermPort : Return.ValidTerm (IDX TERM) (PortTy dir) -> Void
isTermPort IsModuleTy impossible

isTermNat : Return.ValidTerm (IDX TERM) NatTy -> Void
isTermNat IsModuleTy impossible

isTermBool : Return.ValidTerm (IDX TERM) BoolTy -> Void
isTermBool IsModuleTy impossible

isTermFuncParam : (Return.ValidTerm (IDX TERM) return -> Void)
             -> Return.ValidTerm (IDX TERM) (FuncParamTy u param return)
             -> Void
isTermFuncParam f (IsFuncParamTy p x) = f x

isTermFuncParamErr : (Argument.Default.ValidTerm u param -> Void)
                -> Return.ValidTerm (IDX TERM) (FuncParamTy u param return)
                -> Void
isTermFuncParamErr f (IsFuncParamTy x y) = f x

isTermFunc : (Return.ValidTerm (IDX TERM) return -> Void)
          -> Return.ValidTerm (IDX TERM) (FuncTy param return)
          -> Void
isTermFunc f (IsFuncTy p x) = f x

isTermFuncErr : (Argument.ValidTerm (IDX TERM) param -> Void)
             -> Return.ValidTerm (IDX TERM) (FuncTy param return)
             -> Void
isTermFuncErr f (IsFuncTy x y) = f x

export
validTerm : (level : Universe)
         -> (type  : TYPE level)
                  -> DecInfo Return.ValidTerm.Error
                             (Return.ValidTerm level type)
validTerm (DATA _) type = No IsData isTermData
validTerm (IDX TYPE) type = No IsTerm isTermTerm

validTerm (IDX TERM) ChanTy = No IsChan isTermChan
validTerm (IDX TERM) (PortTy dir) = No IsPort isTermPort
validTerm (IDX TERM) NatTy = No IsNat isTermNat
validTerm (IDX TERM) BoolTy = No IsBool isTermBool

validTerm (IDX TERM) UnitTy = Yes IsUnitTy

validTerm (IDX TERM) ModuleTy = Yes IsModuleTy

validTerm (IDX TERM) (FuncParamTy u param return) with (Argument.Default.validTerm u param)
  validTerm (IDX TERM) (FuncParamTy u param return) | (Yes prfP) with (Return.validTerm (IDX TERM) return)
    validTerm (IDX TERM) (FuncParamTy u param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncParamTy prfP prfR)
    validTerm (IDX TERM) (FuncParamTy u param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTermFuncParam prfWhyNot)

  validTerm (IDX TERM) (FuncParamTy u param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncQ msgWhyNot) (isTermFuncParamErr prfWhyNot)

validTerm (IDX TERM) (FuncTy param return) with (Argument.validTerm (IDX TERM) param)
  validTerm (IDX TERM) (FuncTy param return) | (Yes prfP) with (Return.validTerm (IDX TERM) return)
    validTerm (IDX TERM) (FuncTy param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncTy prfP prfR)

    validTerm (IDX TERM) (FuncTy param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTermFunc prfWhyNot)

  validTerm (IDX TERM) (FuncTy param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncP msgWhyNot) (isTermFuncErr prfWhyNot)


-- [ EOF ]
