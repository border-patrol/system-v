module SystemV.HigherOrder.Types.Function

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

mutual
  namespace Argument
    namespace Type
      public export
      data Valid : (level : Universe)
                -> (type  : TYPE level)
                         -> Type
        where

          IsPortTyDesc : Argument.Type.Valid (IDX TYPE) (PortTyDesc type dir)
          IsUnitTyDesc : Argument.Type.Valid (IDX TYPE) UnitTyDesc
          IsFuncTyDesc : Function.Type.Valid (IDX TYPE) (FuncTy param return)
                      -> Argument.Type.Valid (IDX TYPE) (FuncTy param return)

      public export
      data Error = IsData | IsTerm | IsModule | IsChan
                 | IsErrFunc Function.Type.Error

  namespace Returned
    namespace Type
      public export
      data Valid : (level : Universe)
                -> (type  : TYPE level)
                         -> Type
        where
          IsModuleTyDesc : Returned.Type.Valid (IDX TYPE) ModuleTyDesc
          IsFuncTyDesc   : Function.Type.Valid (IDX TYPE) (FuncTy param return)
                        -> Returned.Type.Valid (IDX TYPE) (FuncTy param return)

      public export
      data Error = IsData | IsTerm | IsChan | IsPort | IsNat | IsUnit
                 | IsErrFunc Function.Type.Error

  namespace Function
    namespace Type
      public export
      data Valid : (level : Universe)
                -> (type  : TYPE level)
                         -> Type
        where
          IsFuncTyDesc : Argument.Type.Valid (IDX TYPE) param
                      -> Returned.Type.Valid (IDX TYPE) return
                      -> Function.Type.Valid (IDX TYPE) (FuncTy param return)

      public export
      data Error = InvalidArgument Argument.Type.Error
                 | InvalidReturn   Returned.Type.Error
                 | IsData
                 | IsTerm
                 | IsModule
                 | IsChan
                 | IsUnit
                 | IsPort

mutual
  namespace Argument
    namespace Type
      isData : Argument.Type.Valid (DATA level) type -> Void
      isData IsPortTyDesc impossible

      isTerm : Argument.Type.Valid (IDX TERM) type -> Void
      isTerm IsPortTyDesc impossible

      isModule : Argument.Type.Valid (IDX TYPE) ModuleTyDesc -> Void
      isModule IsPortTyDesc impossible

      isChan : Argument.Type.Valid (IDX TYPE) (ChanTyDesc type) -> Void
      isChan IsPortTyDesc impossible

      isInvalidFunc : (Function.Type.Valid (IDX TYPE) (FuncTy p r) -> Void)
                   -> Argument.Type.Valid (IDX TYPE) (FuncTy p r)
                   -> Void
      isInvalidFunc f (IsFuncTyDesc x) = f x

      export
      valid : (level : Universe)
           -> (type  : TYPE level)
                    -> DecInfo Argument.Type.Error
                              (Argument.Type.Valid level type)
      valid (DATA level) type
        = No IsData isData

      valid (IDX TERM) type
        = No IsTerm isTerm

      valid (IDX TYPE) ModuleTyDesc
        = No IsModule isModule

      valid (IDX TYPE) (ChanTyDesc type)
        = No IsChan isChan

      valid (IDX TYPE) (PortTyDesc type dir)
        = Yes IsPortTyDesc

      valid (IDX TYPE) UnitTyDesc = Yes IsUnitTyDesc

      valid (IDX TYPE) (FuncTy p r) with (Function.Type.valid (IDX TYPE) (FuncTy p r))
        valid (IDX TYPE) (FuncTy p r) | (Yes prfWhy)
          = Yes (IsFuncTyDesc prfWhy)
        valid (IDX TYPE) (FuncTy p r) | (No msgWhyNot prfWhyNot)
          = No (IsErrFunc msgWhyNot) (isInvalidFunc prfWhyNot)

  namespace Returned
    namespace Type

      isData : Returned.Type.Valid (DATA level) type -> Void
      isData IsModuleTyDesc impossible

      isTerm : Returned.Type.Valid (IDX TERM) type -> Void
      isTerm IsModuleTyDesc impossible

      isUnit : Returned.Type.Valid (IDX TYPE) UnitTyDesc -> Void
      isUnit IsModuleTyDesc impossible

      isChan : Returned.Type.Valid (IDX TYPE) (ChanTyDesc type) -> Void
      isChan IsModuleTyDesc impossible

      isPort : Returned.Type.Valid (IDX TYPE) (PortTyDesc type dir) -> Void
      isPort IsModuleTyDesc impossible

      isInvalidFunc : (Function.Type.Valid (IDX TYPE) (FuncTy param return) -> Void)
                    -> Returned.Type.Valid (IDX TYPE) (FuncTy param return)
                    -> Void
      isInvalidFunc f (IsFuncTyDesc x) = f x

      export
      valid : (level : Universe)
           -> (type  : TYPE level)
                    -> DecInfo Returned.Type.Error
                              (Returned.Type.Valid level type)
      valid (DATA level) type
        = No IsData isData

      valid (IDX TERM) type
        = No IsTerm isTerm

      valid (IDX TYPE) (ChanTyDesc type)
        = No IsChan isChan

      valid (IDX TYPE) (PortTyDesc type dir)
        = No IsPort isPort

      valid (IDX TYPE) UnitTyDesc
        = No IsUnit isUnit

      valid (IDX TYPE) ModuleTyDesc
        = Yes IsModuleTyDesc

      valid (IDX TYPE) (FuncTy param return) with (Function.Type.valid (IDX TYPE) (FuncTy param return))
        valid (IDX TYPE) (FuncTy param return) | (Yes prfWhy)
          = Yes (IsFuncTyDesc prfWhy)
        valid (IDX TYPE) (FuncTy param return) | (No msgWhyNot prfWhyNot)
          = No (IsErrFunc msgWhyNot) (isInvalidFunc prfWhyNot)

  namespace Function
    namespace Type

      isData : Function.Type.Valid (DATA level) type -> Void
      isData (IsFuncTyDesc x y) impossible

      isTerm : Function.Type.Valid (IDX TERM) type -> Void
      isTerm (IsFuncTyDesc x y) impossible

      isChan : Function.Type.Valid (IDX TYPE) (ChanTyDesc type) -> Void
      isChan (IsFuncTyDesc x y) impossible

      isModule : Function.Type.Valid (IDX TYPE) ModuleTyDesc -> Void
      isModule (IsFuncTyDesc x y) impossible

      isPort : Function.Type.Valid (IDX TYPE) (PortTyDesc type dir) -> Void
      isPort (IsFuncTyDesc x y) impossible

      isUnit : Function.Type.Valid (IDX TYPE) UnitTyDesc -> Void
      isUnit (IsFuncTyDesc x y) impossible

      invalidArgument : (Argument.Type.Valid (IDX TYPE) param -> Void)
                      -> Function.Type.Valid (IDX TYPE) (FuncTy param return) -> Void
      invalidArgument f (IsFuncTyDesc x y) = f x

      invalidReturn : (Returned.Type.Valid (IDX TYPE) return -> Void)
                    -> Function.Type.Valid (IDX TYPE) (FuncTy param return) -> Void
      invalidReturn f (IsFuncTyDesc x y) = f y

      export
      valid : (level : Universe)
           -> (type  : TYPE level)
                    -> DecInfo Function.Type.Error
                              (Function.Type.Valid level type)
      valid (DATA level) type
        = No IsData isData

      valid (IDX TERM) type
        = No IsTerm isTerm

      valid (IDX TYPE) ModuleTyDesc
        = No IsModule isModule

      valid (IDX TYPE) (ChanTyDesc type)
        = No IsChan isChan

      valid (IDX TYPE) (PortTyDesc type dir)
        = No IsPort isPort

      valid (IDX TYPE) UnitTyDesc
        = No IsUnit isUnit

      valid (IDX TYPE) (FuncTy param return) with (Argument.Type.valid (IDX TYPE) param)
        valid (IDX TYPE) (FuncTy param return) | (Yes prfA) with (Returned.Type.valid (IDX TYPE) return)
          valid (IDX TYPE) (FuncTy param return) | (Yes prfA) | (Yes prfR)
            = Yes (IsFuncTyDesc prfA prfR)

          valid (IDX TYPE) (FuncTy param return) | (Yes prfA) | (No msgWhyNot prfWhyNot)
            = No (InvalidReturn msgWhyNot) (invalidReturn prfWhyNot)

        valid (IDX TYPE) (FuncTy param return) | (No msgWhyNot prfWhyNot)
          = No (InvalidArgument msgWhyNot) (invalidArgument prfWhyNot)


mutual
  namespace Argument
    namespace Term
      public export
      data Valid : (level : Universe)
                -> (type  : TYPE level)
                         -> Type
        where

          IsPortTy : Argument.Term.Valid (IDX TERM) (PortTy type dir)
          IsUnitTy : Argument.Term.Valid (IDX TERM) UnitTy
          IsFuncTy : Function.Term.Valid (IDX TERM) (FuncTy param return)
                      -> Argument.Term.Valid (IDX TERM) (FuncTy param return)

      public export
      data Error = IsData | IsType | IsModule | IsChan
                 | IsErrFunc Function.Term.Error

  namespace Returned
    namespace Term
      public export
      data Valid : (level : Universe)
                -> (type  : TYPE level)
                         -> Type
        where
          IsModuleTy : Returned.Term.Valid (IDX TERM) ModuleTy
          IsFuncTy   : Function.Term.Valid (IDX TERM) (FuncTy param return)
                        -> Returned.Term.Valid (IDX TERM) (FuncTy param return)

      public export
      data Error = IsData | IsType | IsChan | IsPort | IsNat | IsUnit
                 | IsErrFunc Function.Term.Error

  namespace Function
    namespace Term
      public export
      data Valid : (level : Universe)
                -> (type  : TYPE level)
                         -> Type
        where
          IsFuncTy : Argument.Term.Valid (IDX TERM) param
                      -> Returned.Term.Valid (IDX TERM) return
                      -> Function.Term.Valid (IDX TERM) (FuncTy param return)

      public export
      data Error = InvalidArgument Argument.Term.Error
                 | InvalidReturn   Returned.Term.Error
                 | IsData
                 | IsType
                 | IsModule
                 | IsChan
                 | IsUnit
                 | IsPort

mutual
  namespace Argument
    namespace Term
      isData : Argument.Term.Valid (DATA level) type -> Void
      isData IsPortTy impossible

      isType : Argument.Term.Valid (IDX TYPE) type -> Void
      isType IsPortTy impossible

      isModule : Argument.Term.Valid (IDX TERM) ModuleTy -> Void
      isModule IsPortTy impossible

      isChan : Argument.Term.Valid (IDX TERM) (ChanTy type) -> Void
      isChan IsPortTy impossible

      isInvalidFunc : (Function.Term.Valid (IDX TERM) (FuncTy p r) -> Void)
                   -> Argument.Term.Valid (IDX TERM) (FuncTy p r)
                   -> Void
      isInvalidFunc f (IsFuncTy x) = f x

      export
      valid : (level : Universe)
           -> (type  : TYPE level)
                    -> DecInfo Argument.Term.Error
                              (Argument.Term.Valid level type)
      valid (DATA level) type
        = No IsData isData

      valid (IDX TYPE) type
        = No IsType isType

      valid (IDX TERM) ModuleTy
        = No IsModule isModule

      valid (IDX TERM) (ChanTy type)
        = No IsChan isChan

      valid (IDX TERM) (PortTy type dir)
        = Yes IsPortTy

      valid (IDX TERM) UnitTy = Yes IsUnitTy

      valid (IDX TERM) (FuncTy p r) with (Function.Term.valid (IDX TERM) (FuncTy p r))
        valid (IDX TERM) (FuncTy p r) | (Yes prfWhy)
          = Yes (IsFuncTy prfWhy)
        valid (IDX TERM) (FuncTy p r) | (No msgWhyNot prfWhyNot)
          = No (IsErrFunc msgWhyNot) (isInvalidFunc prfWhyNot)

  namespace Returned
    namespace Term

      isData : Returned.Term.Valid (DATA level) type -> Void
      isData IsModuleTy impossible

      isType : Returned.Term.Valid (IDX TYPE) type -> Void
      isType IsModuleTy impossible

      isUnit : Returned.Term.Valid (IDX TERM) UnitTy -> Void
      isUnit IsModuleTy impossible

      isChan : Returned.Term.Valid (IDX TERM) (ChanTy type) -> Void
      isChan IsModuleTy impossible

      isPort : Returned.Term.Valid (IDX TERM) (PortTy type dir) -> Void
      isPort IsModuleTy impossible

      isInvalidFunc : (Function.Term.Valid (IDX TERM) (FuncTy param return) -> Void)
                    -> Returned.Term.Valid (IDX TERM) (FuncTy param return)
                    -> Void
      isInvalidFunc f (IsFuncTy x) = f x

      export
      valid : (level : Universe)
           -> (type  : TYPE level)
                    -> DecInfo Returned.Term.Error
                              (Returned.Term.Valid level type)
      valid (DATA level) type
        = No IsData isData

      valid (IDX TYPE) type
        = No IsType isType

      valid (IDX TERM) (ChanTy type)
        = No IsChan isChan

      valid (IDX TERM) (PortTy type dir)
        = No IsPort isPort

      valid (IDX TERM) UnitTy
        = No IsUnit isUnit

      valid (IDX TERM) ModuleTy
        = Yes IsModuleTy

      valid (IDX TERM) (FuncTy param return) with (Function.Term.valid (IDX TERM) (FuncTy param return))
        valid (IDX TERM) (FuncTy param return) | (Yes prfWhy)
          = Yes (IsFuncTy prfWhy)
        valid (IDX TERM) (FuncTy param return) | (No msgWhyNot prfWhyNot)
          = No (IsErrFunc msgWhyNot) (isInvalidFunc prfWhyNot)

  namespace Function
    namespace Term

      isData : Function.Term.Valid (DATA level) type -> Void
      isData (IsFuncTy x y) impossible

      isType : Function.Term.Valid (IDX TYPE) type -> Void
      isType (IsFuncTy x y) impossible

      isChan : Function.Term.Valid (IDX TERM) (ChanTy type) -> Void
      isChan (IsFuncTy x y) impossible

      isModule : Function.Term.Valid (IDX TERM) ModuleTy -> Void
      isModule (IsFuncTy x y) impossible

      isPort : Function.Term.Valid (IDX TERM) (PortTy type dir) -> Void
      isPort (IsFuncTy x y) impossible

      isUnit : Function.Term.Valid (IDX TERM) UnitTy -> Void
      isUnit (IsFuncTy x y) impossible

      invalidArgument : (Argument.Term.Valid (IDX TERM) param -> Void)
                      -> Function.Term.Valid (IDX TERM) (FuncTy param return) -> Void
      invalidArgument f (IsFuncTy x y) = f x

      invalidReturn : (Returned.Term.Valid (IDX TERM) return -> Void)
                    -> Function.Term.Valid (IDX TERM) (FuncTy param return) -> Void
      invalidReturn f (IsFuncTy x y) = f y

      export
      valid : (level : Universe)
           -> (type  : TYPE level)
                    -> DecInfo Function.Term.Error
                              (Function.Term.Valid level type)
      valid (DATA level) type
        = No IsData isData

      valid (IDX TYPE) type
        = No IsType isType

      valid (IDX TERM) ModuleTy
        = No IsModule isModule

      valid (IDX TERM) (ChanTy type)
        = No IsChan isChan

      valid (IDX TERM) (PortTy type dir)
        = No IsPort isPort

      valid (IDX TERM) UnitTy
        = No IsUnit isUnit

      valid (IDX TERM) (FuncTy param return) with (Argument.Term.valid (IDX TERM) param)
        valid (IDX TERM) (FuncTy param return) | (Yes prfA) with (Returned.Term.valid (IDX TERM) return)
          valid (IDX TERM) (FuncTy param return) | (Yes prfA) | (Yes prfR)
            = Yes (IsFuncTy prfA prfR)

          valid (IDX TERM) (FuncTy param return) | (Yes prfA) | (No msgWhyNot prfWhyNot)
            = No (InvalidReturn msgWhyNot) (invalidReturn prfWhyNot)

        valid (IDX TERM) (FuncTy param return) | (No msgWhyNot prfWhyNot)
          = No (InvalidArgument msgWhyNot) (invalidArgument prfWhyNot)

-- [ EOF ]
