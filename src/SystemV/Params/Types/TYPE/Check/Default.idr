module SystemV.Params.Types.TYPE.Check.Default

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Params.Types.TYPE
import SystemV.Params.Types.TYPE.Equality

import SystemV.Params.Types.TYPE.Check.Types

%default total

||| A predicate to type check types against type formers.
public export
data TyCheck : (typeLevel, valueLevel : Universe)
            -> (type  : TYPE typeLevel)
            -> (value : TYPE valueLevel)
            -> Type
  where
    IsData : Equals Universe TYPE type value
          -> Default.TyCheck (DATA TYPE) (DATA TYPE) type value

    IsNat : Types.TyCheck   (NatTyDesc n) (NatTy m)
         -> Default.TyCheck (IDX TYPE) (IDX TERM) (NatTyDesc n) (NatTy m)

public export
data Error = WrongType (TYPE u) (TYPE v)

leftMustBeType : (typeLevel = valueLevel -> Void)
              -> (IDX TYPE = typeLevel -> Void)
              -> TyCheck typeLevel valueLevel type value
              -> Void
leftMustBeType f g (IsData (Same Refl Refl)) = f Refl
leftMustBeType f g (IsNat (ChkNat prf)) = g Refl

rightMustBeValue : (IDX TERM = valueLevel -> Void)
                -> TyCheck (IDX TYPE) valueLevel type value
                -> Void
rightMustBeValue g (IsNat (ChkNat prf)) = g Refl

doesNotCheck : (TyCheck type value -> Void)
            -> TyCheck (IDX TYPE) (IDX TERM) type value
            -> Void
doesNotCheck f (IsNat (ChkNat prf)) = f (ChkNat prf)

isNotNat : (prfWhy : TyCheck type value) -> (CheckedNat prfWhy -> Void) -> TyCheck (IDX TYPE) (IDX TERM) type value -> Void
isNotNat (ChkNat Refl) f (IsNat (ChkNat Refl)) = f IsCheckedNat

dataTypesDiffer : (Equals Universe TYPE type value -> Void) -> TyCheck (DATA TYPE) (DATA TYPE) type value -> Void
dataTypesDiffer f (IsData x) = f x

cannotBothBeTerm : TyCheck (DATA TERM) (DATA TERM) type value -> Void
cannotBothBeTerm (IsData x) impossible
cannotBothBeTerm (IsNat x) impossible

cannotBothBeType : TyCheck (IDX ty) (IDX ty) type value -> Void
cannotBothBeType (IsData x) impossible
cannotBothBeType (IsNat x) impossible


export
tyCheck : (typeLevel, valueLevel : Universe)
       -> (type  : TYPE typeLevel)
       -> (value : TYPE valueLevel)
                -> DecInfo Default.Error
                           (Default.TyCheck typeLevel valueLevel type value)
tyCheck typeLevel valueLevel type value with (Universe.decEq typeLevel valueLevel)
  tyCheck valueLevel valueLevel type value | (Yes Refl) with (valueLevel)
    tyCheck valueLevel valueLevel type value | (Yes Refl) | (DATA TERM)
      = No (WrongType type value ) (cannotBothBeTerm)

    tyCheck valueLevel valueLevel type value | (Yes Refl) | (DATA TYPE) with (Equality.decEq type value)
      tyCheck valueLevel valueLevel type value | (Yes Refl) | (DATA TYPE) | (Yes prfWhy) = Yes (IsData prfWhy)

      tyCheck valueLevel valueLevel type value | (Yes Refl) | (DATA TYPE) | (No msgWhyNot prfWhyNot)
        = No (WrongType type value ) (dataTypesDiffer prfWhyNot)

    tyCheck valueLevel valueLevel type value | (Yes Refl) | (IDX _)
      = No (WrongType type value) (cannotBothBeType)

  tyCheck typeLevel valueLevel type value | (No contra) with (Universe.decEq (IDX TYPE) typeLevel)
    tyCheck typeLevel valueLevel type value | (No contra) | (Yes prf) with (prf)
      tyCheck (IDX TYPE) valueLevel type value | (No contra) | (Yes prf) | Refl with (Universe.decEq (IDX TERM) valueLevel)
        tyCheck (IDX TYPE) valueLevel type value | (No contra) | (Yes prf) | Refl | (Yes x) with (x)
          tyCheck (IDX TYPE) (IDX TERM) type value | (No contra) | (Yes prf) | Refl | (Yes x) | Refl with (Types.typeCheck type value)
            tyCheck (IDX TYPE) (IDX TERM) type value | (No contra) | (Yes prf) | Refl | (Yes x) | Refl | (Yes prfWhy) with (isCheckedNat prfWhy)
              tyCheck (IDX TYPE) (IDX TERM) (NatTyDesc n) (NatTy n) | (No contra) | (Yes prf) | Refl | (Yes x) | Refl | (Yes (ChkNat Refl)) | (Yes IsCheckedNat)
                = Yes (IsNat (ChkNat Refl))

              tyCheck (IDX TYPE) (IDX TERM) type value | (No contra) | (Yes prf) | Refl | (Yes x) | Refl | (Yes prfWhy) | (No f)
                = No (WrongType type value) (isNotNat prfWhy f)

            tyCheck (IDX TYPE) (IDX TERM) type value | (No contra) | (Yes prf) | Refl | (Yes x) | Refl | (No msgWhyNot prfWhyNot)
              = No (WrongType type value) (doesNotCheck prfWhyNot)

        tyCheck (IDX TYPE) valueLevel type value | (No contra) | (Yes prf) | Refl | (No f)
          = No (WrongType type value) (rightMustBeValue f)

    tyCheck typeLevel valueLevel type value | (No contra) | (No f)
      = No (WrongType type value) (leftMustBeType contra f)

-- [ EOF ]
