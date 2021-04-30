module SystemV.Params.Evaluation.Indexing

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden
import SystemV.Params.Evaluation.Values.Predicates

%default total

public export
data Args : (idx   : SystemV Nil (NatTy n))
         -> (prfIV : Value idx)
         -> (port  : SystemV Nil (PortTy (VectorTyDesc s datatype) dir))
         -> (prfP  : Value port)
                  -> Type
  where
    NoChange : LTE (S n) s
            -> Args (MkNat n)                    MkNat
                    (MkPort (TyVect s type) dir) (MkPort (TyVect s datatype) dir)

    OverIdx : LTE (S m) s -> Args (NatOverride m)              (NatOverride)
                                  (MkPort (TyVect s type) dir) (MkPort (TyVect s datatype) dir)

    OverTy : {type     : SystemV Nil (VectorTyDesc o typetype)}
          -> {datatype : Value type}
          -> IsNotOverridden (VectorTyDesc o typetype) type datatype
          -> LTE (S n) o
          -> Args (MkNat n)                        MkNat
                  (MkPort (TyOverride type) dir) (MkPort (TyOverride datatype) dir)

    OverBoth : {type     : SystemV Nil (VectorTyDesc o typetype)}
            -> {datatype : Value type}
            -> IsNotOverridden (VectorTyDesc o typetype) type datatype
            -> LTE (S m) o
                        -> Args (NatOverride m)                (NatOverride)
                                (MkPort (TyOverride type) dir) (MkPort (TyOverride datatype) dir)

export
validArgs : (idx   : SystemV Nil (NatTy n))
         -> (prfIV : Value idx)
         -> (port  : SystemV Nil (PortTy (VectorTyDesc s datatype) dir))
         -> (prfP  : Value port)
                  -> Maybe (Args idx prfIV port prfP)
-- reminder we must check for sequences
-- overrides cannot contain overrides
validArgs idx prfIV port prfP with (isNat prfIV)
  validArgs idx prfIV port prfP | (Yes prf) with (isPort prfP)
    validArgs idx prfIV (MkPort datatypeTerm dir) (MkPort datatypeValue dir) | (Yes prf) | (Yes ItIs) with (Alt.overridden datatypeValue)
      validArgs (MkNat n) MkNat (MkPort (TyOverride term) dir) (MkPort (TyOverride val) dir) | (Yes ItIsPure) | (Yes ItIs) | IsOver with (Alt.overridden val)
        validArgs (MkNat n) MkNat (MkPort (TyOverride (TyVect o ty)) dir) (MkPort (TyOverride (TyVect o tyv)) dir) | (Yes ItIsPure) | (Yes ItIs) | IsOver | IsVect with (isLTE (S n) o)
          validArgs (MkNat n) MkNat (MkPort (TyOverride (TyVect o ty)) dir) (MkPort (TyOverride (TyVect o tyv)) dir) | (Yes ItIsPure) | (Yes ItIs) | IsOver | IsVect | (Yes prf)
            = Just (OverTy ItIsVect prf)
          validArgs (MkNat n) MkNat (MkPort (TyOverride (TyVect o ty)) dir) (MkPort (TyOverride (TyVect o tyv)) dir) | (Yes ItIsPure) | (Yes ItIs) | IsOver | IsVect | (No contra)
            = Nothing
        validArgs (MkNat n) MkNat (MkPort (TyOverride _) dir) (MkPort (TyOverride _) dir) | (Yes ItIsPure) | (Yes ItIs) | IsOver | alt
          = Nothing

      validArgs (NatOverride m) NatOverride (MkPort (TyOverride term) dir) (MkPort (TyOverride val) dir) | (Yes ItIsOver) | (Yes ItIs) | IsOver with (Alt.overridden val)
        validArgs (NatOverride m) NatOverride (MkPort (TyOverride (TyVect o term)) dir) (MkPort (TyOverride (TyVect o valuev)) dir) | (Yes ItIsOver) | (Yes ItIs) | IsOver | IsVect with (isLTE (S m) o)
          validArgs (NatOverride m) NatOverride (MkPort (TyOverride (TyVect o term)) dir) (MkPort (TyOverride (TyVect o valuev)) dir) | (Yes ItIsOver) | (Yes ItIs) | IsOver | IsVect | (Yes prf)
            = Just (OverBoth ItIsVect prf)
          validArgs (NatOverride m) NatOverride (MkPort (TyOverride (TyVect o term)) dir) (MkPort (TyOverride (TyVect o valuev)) dir) | (Yes ItIsOver) | (Yes ItIs) | IsOver | IsVect | (No contra)
            = Nothing
        validArgs (NatOverride m) NatOverride (MkPort (TyOverride term) dir) (MkPort (TyOverride val) dir) | (Yes ItIsOver) | (Yes ItIs) | IsOver | alt
          = Nothing

      validArgs (MkNat n) MkNat (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyv) dir) | (Yes ItIsPure) | (Yes ItIs) | IsVect with (isLTE (S n) s)
        validArgs (MkNat n) MkNat (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyv) dir) | (Yes ItIsPure) | (Yes ItIs) | IsVect | (Yes prf)
          = Just (NoChange prf)
        validArgs (MkNat n) MkNat (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyv) dir) | (Yes ItIsPure) | (Yes ItIs) | IsVect | (No contra)
          = Nothing

      validArgs (NatOverride m) NatOverride (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyv) dir) | (Yes ItIsOver) | (Yes ItIs) | IsVect with (isLTE (S m) s)
        validArgs (NatOverride m) NatOverride (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyv) dir) | (Yes ItIsOver) | (Yes ItIs) | IsVect | (Yes prf)
          = Just (OverIdx prf)
        validArgs (NatOverride m) NatOverride (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyv) dir) | (Yes ItIsOver) | (Yes ItIs) | IsVect | (No contra)
          = Nothing

    validArgs idx prfIV port prfP | (Yes prf) | (No contra)
      = Nothing

  validArgs idx prfIV port prfP | (No contra)
    = Nothing


public export
index : (idx   : SystemV Nil (NatTy n))
     -> (prfIV : Value idx)
     -> (port  : SystemV Nil (PortTy (VectorTyDesc s datatype) dir))
     -> (prfP  : Value port)
     -> (prf   : Args idx prfIV port prfP)
              -> SystemV Nil (PortTy datatype dir)
index idx prfIV port prfP prf with (prf)
  index (MkNat n) MkNat (MkPort (TyVect s term) dir) (MkPort (TyVect s val) dir) prf | (NoChange x)
    = MkPort term dir
  index (NatOverride m) NatOverride (MkPort (TyVect s term) dir) (MkPort (TyVect s value) dir) prf | (OverIdx x)
    = MkPort term dir
  index (MkNat n) MkNat (MkPort (TyOverride term) dir) (MkPort (TyOverride value) dir) prf | (OverTy x y) with (x)
    index (MkNat n) MkNat (MkPort (TyOverride (TyVect o term)) dir) (MkPort (TyOverride (TyVect o value)) dir) prf | (OverTy x y) | ItIsVect
      = MkPort (TyOverride term) dir

  index (NatOverride m) NatOverride (MkPort (TyOverride term) dir) (MkPort (TyOverride value) dir) prf | (OverBoth x y) with (x)
    index (NatOverride m) NatOverride (MkPort (TyOverride (TyVect o term)) dir) (MkPort (TyOverride (TyVect o value)) dir) prf | (OverBoth x y) | ItIsVect
      = MkPort (TyOverride term) dir

-- [ EOF ]
