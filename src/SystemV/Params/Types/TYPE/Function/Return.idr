module SystemV.Params.Types.TYPE.Function.Return

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Params.Types.TYPE

import SystemV.Params.Types.TYPE.Function.Argument
import SystemV.Params.Types.TYPE.Function.Argument.Default

%default total

public export
data ValidType : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsModuleTyDesc : Return.ValidType (IDX TYPE) ModuleTyDesc
    IsUnitTyDesc   : Return.ValidType (IDX TYPE) UnitTyDesc

    IsFuncDefTyDesc : Argument.Default.ValidType u param
                   -> Return.ValidType (IDX TYPE) return
                   -> Return.ValidType (IDX TYPE) (FuncDefTy u param return)

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
isTyDescData IsUnitTyDesc impossible
isTyDescData (IsFuncDefTyDesc p x) impossible
isTyDescData (IsFuncTyDesc o x) impossible

isTyDescTerm : Return.ValidType (IDX TERM) type -> Void
isTyDescTerm IsModuleTyDesc impossible
isTyDescTerm IsUnitTyDesc impossible
isTyDescTerm (IsFuncDefTyDesc p x) impossible
isTyDescTerm (IsFuncTyDesc p x) impossible

isTyDescChan : Return.ValidType (IDX TYPE) (ChanTyDesc type) -> Void
isTyDescChan IsModuleTyDesc impossible
isTyDescChan IsUnitTyDesc impossible
isTyDescChan (IsFuncDefTyDesc p x) impossible
isTyDescChan (IsFuncTyDesc p x) impossible

isTyDescBool : Return.ValidType (IDX TYPE) BoolTyDesc -> Void
isTyDescBool IsModuleTyDesc impossible
isTyDescBool IsUnitTyDesc impossible
isTyDescBool (IsFuncDefTyDesc p x) impossible
isTyDescBool (IsFuncTyDesc p x) impossible

isTyDescPort : Return.ValidType (IDX TYPE) (PortTyDesc type dir) -> Void
isTyDescPort IsModuleTyDesc impossible
isTyDescPort IsUnitTyDesc impossible
isTyDescPort (IsFuncDefTyDesc p x) impossible
isTyDescPort (IsFuncTyDesc p x) impossible

isTyDescNat : Return.ValidType (IDX TYPE) (NatTyDesc k) -> Void
isTyDescNat IsModuleTyDesc impossible
isTyDescNat IsUnitTyDesc impossible
isTyDescNat (IsFuncDefTyDesc p x) impossible
isTyDescNat (IsFuncTyDesc p x) impossible

isTyDescFuncDef : (Return.ValidType (IDX TYPE) return -> Void)
               -> Return.ValidType (IDX TYPE) (FuncDefTy u param return)
               -> Void
isTyDescFuncDef f (IsFuncDefTyDesc p x) = f x

isTyDescFuncDefP : (Argument.Default.ValidType u param -> Void)
                -> Return.ValidType (IDX TYPE) (FuncDefTy u param return)
                -> Void
isTyDescFuncDefP f (IsFuncDefTyDesc x y) = f x

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

validType (IDX TYPE) (ChanTyDesc type) = No IsChan isTyDescChan
validType (IDX TYPE) (PortTyDesc type dir) = No IsPort isTyDescPort
validType (IDX TYPE) (NatTyDesc k) = No IsNat isTyDescNat
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

validType (IDX TYPE) (FuncDefTy u param return) with (Argument.Default.validType u param)
  validType (IDX TYPE) (FuncDefTy u param return) | (Yes prfP) with (Return.validType (IDX TYPE) return)
    validType (IDX TYPE) (FuncDefTy u param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncDefTyDesc prfP prfR)

    validType (IDX TYPE) (FuncDefTy u param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTyDescFuncDef prfWhyNot)

  validType (IDX TYPE) (FuncDefTy u param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncQ msgWhyNot) (isTyDescFuncDefP prfWhyNot)

public export
data ValidTerm : (level : Universe)
              -> (type  : TYPE level)
                       -> Type
  where
    IsModuleTy : Return.ValidTerm (IDX TERM) ModuleTy
    IsUnitTy   : Return.ValidTerm (IDX TERM) UnitTy

    IsFuncDefTy : Argument.Default.ValidTerm u param
               -> Return.ValidTerm (IDX TERM) return
               -> Return.ValidTerm (IDX TERM) (FuncDefTy u param return)

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
isTermData IsUnitTy impossible
isTermData (IsFuncDefTy p x) impossible
isTermData (IsFuncTy p x) impossible

isTermTerm : Return.ValidTerm (IDX TYPE) type -> Void
isTermTerm IsModuleTy impossible
isTermTerm IsUnitTy impossible
isTermTerm (IsFuncDefTy p x) impossible
isTermTerm (IsFuncTy p x) impossible

isTermChan : Return.ValidTerm (IDX TERM) (ChanTy type) -> Void
isTermChan IsModuleTy impossible
isTermChan IsUnitTy impossible
isTermChan (IsFuncDefTy p x) impossible
isTermChan (IsFuncTy p x) impossible

isTermPort : Return.ValidTerm (IDX TERM) (PortTy type dir) -> Void
isTermPort IsModuleTy impossible
isTermPort IsUnitTy impossible
isTermPort (IsFuncDefTy p x) impossible
isTermPort (IsFuncTy p x) impossible

isTermNat : Return.ValidTerm (IDX TERM) (NatTy k) -> Void
isTermNat IsModuleTy impossible
isTermNat IsUnitTy impossible
isTermNat (IsFuncDefTy p x) impossible
isTermNat (IsFuncTy p x) impossible

isTermBool : Return.ValidTerm (IDX TERM) BoolTy -> Void
isTermBool IsModuleTy impossible
isTermBool IsUnitTy impossible
isTermBool (IsFuncDefTy p x) impossible
isTermBool (IsFuncTy p x) impossible


isTermFuncDef : (Return.ValidTerm (IDX TERM) return -> Void)
             -> Return.ValidTerm (IDX TERM) (FuncDefTy u param return)
             -> Void
isTermFuncDef f (IsFuncDefTy p x) = f x

isTermFuncDefErr : (Argument.Default.ValidTerm u param -> Void)
                -> Return.ValidTerm (IDX TERM) (FuncDefTy u param return)
                -> Void
isTermFuncDefErr f (IsFuncDefTy x y) = f x

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

validTerm (IDX TERM) (ChanTy type) = No IsChan isTermChan
validTerm (IDX TERM) (PortTy type dir) = No IsPort isTermPort
validTerm (IDX TERM) (NatTy k) = No IsNat isTermNat
validTerm (IDX TERM) BoolTy = No IsBool isTermBool

validTerm (IDX TERM) UnitTy = Yes IsUnitTy

validTerm (IDX TERM) ModuleTy = Yes IsModuleTy

validTerm (IDX TERM) (FuncDefTy u param return) with (Argument.Default.validTerm u param)
  validTerm (IDX TERM) (FuncDefTy u param return) | (Yes prfP) with (Return.validTerm (IDX TERM) return)
    validTerm (IDX TERM) (FuncDefTy u param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncDefTy prfP prfR)
    validTerm (IDX TERM) (FuncDefTy u param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTermFuncDef prfWhyNot)

  validTerm (IDX TERM) (FuncDefTy u param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncQ msgWhyNot) (isTermFuncDefErr prfWhyNot)

validTerm (IDX TERM) (FuncTy param return) with (Argument.validTerm (IDX TERM) param)
  validTerm (IDX TERM) (FuncTy param return) | (Yes prfP) with (Return.validTerm (IDX TERM) return)
    validTerm (IDX TERM) (FuncTy param return) | (Yes prfP) | (Yes prfR)
      = Yes (IsFuncTy prfP prfR)

    validTerm (IDX TERM) (FuncTy param return) | (Yes prfP) | (No msgWhyNot prfWhyNot)
      = No (IsErrFunc msgWhyNot) (isTermFunc prfWhyNot)

  validTerm (IDX TERM) (FuncTy param return) | (No msgWhyNot prfWhyNot)
    = No (IsErrFuncP msgWhyNot) (isTermFuncErr prfWhyNot)


-- [ EOF ]
