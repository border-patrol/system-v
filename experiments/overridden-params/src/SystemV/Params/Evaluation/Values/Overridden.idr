module SystemV.Params.Evaluation.Values.Overridden

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values

%default total

namespace DataType
  public export
  data Overridden : (type  : (TYPE (DATA TYPE)))
                 -> (term  : SystemV Nil type)
                 -> (value : Value term)
                 -> Type
    where
      IsOverridden : (type : TYPE (DATA TYPE))
                  -> (term : SystemV Nil type)
                  -> (val  : Value term)
                  -> Overridden type' (TyOverride term) (TyOverride val)

  isLogic : Overridden LogicTyDesc TyLogic TyLogic -> Void
  isLogic (IsOverridden type term val) impossible


  isVect : Overridden (VectorTyDesc s ty) (TyVect s y) (TyVect s x) -> Void
  isVect (IsOverridden type term val) impossible


  isTypeDef : Overridden (TypeDefTy ty) (TyTypeDef y) (TyTypeDef x) -> Void
  isTypeDef (IsOverridden type term val) impossible


  export
  overridden : {type  : (TYPE (DATA TYPE))}
            -> {term  : SystemV Nil type}
            -> (value : Value term)
                     -> Dec (Overridden type term value)
  overridden TyLogic = No isLogic
  overridden (TyVect s x) = No isVect
  overridden (TyTypeDef x) = No isTypeDef
  overridden (TyOverride x) = Yes (IsOverridden _ _ x)

namespace Nat
  public export
  data Overridden : (type  : (TYPE (IDX TERM)))
                 -> (term  : SystemV Nil type)
                 -> (value : Value term)
                          -> Type
    where
      IsOverridden : Overridden (NatTy n) (NatOverride m) NatOverride


  mustNotBeSeq : Overridden (NatTy n) (Seq left right) (Seq x y) -> Void
  mustNotBeSeq (IsOverridden) impossible

  isPure : Overridden (NatTy n) (MkNat n) MkNat -> Void
  isPure IsOverridden impossible

  export
  overridden : {term  : SystemV Nil (NatTy n)}
            -> (value : Value term)
                     -> Dec (Overridden (NatTy n) term value)
  overridden MkNat = No isPure
  overridden NatOverride = Yes (IsOverridden)
  overridden (Seq x y) = No mustNotBeSeq

namespace NotData

  data OverriddenNot : (type  : (TYPE (DATA TYPE)))
                    -> (term  : SystemV Nil type)
                    -> (value : Value term)
                    -> Type
    where
      IsNot : (DataType.Overridden type term value -> Void)
           -> OverriddenNot type term value

  isOverridden : Overridden type term value -> OverriddenNot type term value -> Void
  isOverridden x (IsNot f) = f x

  export
  overriddenNot : {type  : (TYPE (DATA TYPE))}
               -> {term  : SystemV Nil type}
               -> (value : Value term)
                        -> Dec (OverriddenNot type term value)
  overriddenNot value with (overridden value)
    overriddenNot value | (Yes prf) = No (isOverridden prf)
    overriddenNot value | (No contra) = Yes (IsNot contra)

namespace NotNat
    public export
    data OverriddenNot : (type  : (TYPE (IDX TERM)))
                      -> (term  : SystemV Nil type)
                      -> (value : Value term)
                               -> Type
      where
        IsOverriddenNot : OverriddenNot (NatTy n) (MkNat n) MkNat

    mustNotBeSeq : OverriddenNot (NatTy n) (Seq left right) (Seq x y) -> Void
    mustNotBeSeq IsOverriddenNot impossible

    isOverridden : OverriddenNot (NatTy n) (NatOverride m) NatOverride -> Void
    isOverridden IsOverriddenNot impossible

    export
    overriddenNot : {term  : SystemV Nil (NatTy n)}
                 -> (value : Value term)
                          -> Dec (OverriddenNot (NatTy n) term value)
    overriddenNot MkNat = Yes IsOverriddenNot
    overriddenNot NatOverride = No isOverridden
    overriddenNot (Seq x y) = No mustNotBeSeq

namespace DataType
  namespace Alt
    public export
    data Overridden : (type  : (TYPE (DATA TYPE)))
                   -> (term  : SystemV Nil type)
                   -> (value : Value term)
                   -> Type
      where
        IsOver  : Alt.Overridden type' (TyOverride term) (TyOverride val)
        IsLogic : Alt.Overridden LogicTyDesc TyLogic TyLogic
        IsVect  : Alt.Overridden (VectorTyDesc s ty) (TyVect s datatype) (TyVect s datatypev)
        IsTDef  : Alt.Overridden (TypeDefTy ty) (TyTypeDef datatype) (TyTypeDef datatypev)

    export
    overridden : {type  : (TYPE (DATA TYPE))}
              -> {term  : SystemV Nil type}
              -> (value : Value term)
                       -> Alt.Overridden type term value
    overridden TyLogic = IsLogic
    overridden (TyVect s x) = IsVect
    overridden (TyTypeDef x) = IsTDef
    overridden (TyOverride x) = IsOver

  public export
  data IsNotOverridden : (type  : (TYPE (DATA TYPE)))
                      -> (term  : SystemV Nil type)
                      -> (value : Value term)
                      -> Type
    where
      ItIsLogic : IsNotOverridden LogicTyDesc TyLogic TyLogic
      ItIsVect  : IsNotOverridden (VectorTyDesc s ty) (TyVect s datatype) (TyVect s datatypev)
      ItIsTDef  : IsNotOverridden (TypeDefTy ty) (TyTypeDef datatype) (TyTypeDef datatypev)

  isOverridden : IsNotOverridden type (TyOverride inner) (TyOverride x) -> Void
  isOverridden ItIsLogic impossible
  isOverridden ItIsVect impossible
  isOverridden ItIsTDef impossible

  export
  isNotOverridden : {type  : (TYPE (DATA TYPE))}
                 -> {term  : SystemV Nil type}
                 -> (value : Value term)
                          -> Dec (IsNotOverridden type term value)
  isNotOverridden TyLogic = Yes ItIsLogic
  isNotOverridden (TyVect s x) = Yes ItIsVect
  isNotOverridden (TyTypeDef x) = Yes ItIsTDef
  isNotOverridden (TyOverride x) = No isOverridden
