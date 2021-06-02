module SystemV.Params.Types.TYPE.Check.Default

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality

import SystemV.Params.Types.TYPE.Check.Types
import SystemV.Params.Types.TYPE.Check.Data

%default total

||| A predicate to type check types against type formers.
public export
data TyCheck : (typeLevel, valueLevel : Universe)
            -> (type  : TYPE typeLevel)
            -> (value : TYPE valueLevel)
            -> Type
  where
    IsNat : Types.TyCheck   (NatTyDesc) (NatTy)
         -> Default.TyCheck (IDX TYPE) (IDX TERM) (NatTyDesc) (NatTy)

    IsData : Data.TyCheckData kind type
          -> Default.TyCheck (DATA TYPE) (DATA TERM) kind type

public export
data Error = WrongType (TYPE u) (TYPE v)
           | UError    Universe.Error


wrongTypes : (ValidLevels typeLevel valueLevel -> Void) -> Default.TyCheck typeLevel valueLevel type value -> Void
wrongTypes f (IsNat x) = f ForNat
wrongTypes f (IsData x) = f ForData

mustBeNat : (prfWhy : TyCheck type value) -> (CheckedNat prfWhy -> Void) -> TyCheck (IDX TYPE) (IDX TERM) type value -> Void
mustBeNat ChkNat f (IsNat ChkNat) = f IsCheckedNat

typeMismatch : (TyCheck type value -> Void) -> TyCheck (IDX TYPE) (IDX TERM) type value -> Void
typeMismatch f (IsNat x) = f x

export
tyCheck : (typeLevel, valueLevel : Universe)
       -> (type  : TYPE typeLevel)
       -> (value : TYPE valueLevel)
                -> DecInfo Default.Error
                           (Default.TyCheck typeLevel valueLevel type value)
tyCheck typeLevel valueLevel type value with (validLevels typeLevel valueLevel)
  tyCheck (IDX TYPE) (IDX TERM) type value | (Yes ForNat) with (Types.typeCheck type value)
    tyCheck (IDX TYPE) (IDX TERM) type value | (Yes ForNat) | (Yes prfWhy) with (isCheckedNat prfWhy)
      tyCheck (IDX TYPE) (IDX TERM) NatTyDesc NatTy | (Yes ForNat) | (Yes ChkNat) | (Yes IsCheckedNat)
        = Yes (IsNat ChkNat)
      tyCheck (IDX TYPE) (IDX TERM) type value | (Yes ForNat) | (Yes prfWhy) | (No contra)
        = No (WrongType type value) (mustBeNat prfWhy contra)

    tyCheck (IDX TYPE) (IDX TERM) type value | (Yes ForNat) | (No msgWhyNot prfWhyNot)
      = No (WrongType type value) (typeMismatch prfWhyNot)

  tyCheck (DATA TYPE) (DATA TERM) DATATYPE DATATERM | (Yes ForData) = Yes (IsData ChkData)

  tyCheck typeLevel valueLevel type value | (No msgWhyNot prfWhyNot)
    = No (UError msgWhyNot) (wrongTypes prfWhyNot)

-- [ EOF ]
