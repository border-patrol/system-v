module SystemV.Params.Evaluation.Sizing

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden
import SystemV.Params.Evaluation.Values.Predicates

%default total

public export
data Args : (port  : SystemV Nil (PortTy (VectorTyDesc s type) dir))
         -> (value : Value port)
                  -> Type
  where
    NoChange : (dtype  : SystemV Nil type)
            -> (dvalue : Value dtype)
                      -> Args (MkPort (TyVect s dtype)  dir)
                              (MkPort (TyVect s dvalue) dir)

    Overridden : {type   : TYPE (DATA TYPE)}
              -> (dtype  : SystemV Nil (VectorTyDesc o type))
              -> (dvalue : Value dtype)
              -> (prf    : IsNotOverridden (VectorTyDesc o type) dtype dvalue)
                        -> Args (MkPort (TyOverride dtype)  dir)
                                (MkPort (TyOverride dvalue) dir)

export
validArgs : (port  : SystemV Nil (PortTy (VectorTyDesc s type) dir))
         -> (value : Value port)
                  -> Maybe (Args port value)
validArgs port value with (isPort value)
  validArgs (MkPort t dir) (MkPort v dir) | (Yes ItIs) with (Alt.overridden v)
    validArgs (MkPort (TyOverride term) dir) (MkPort (TyOverride val) dir) | (Yes ItIs) | IsOver with (Alt.overridden val)
      validArgs (MkPort (TyOverride (TyVect o t)) dir) (MkPort (TyOverride (TyVect o v)) dir) | (Yes ItIs) | IsOver | IsVect
        = Just (Overridden (TyVect o t) (TyVect o v) ItIsVect)

      validArgs (MkPort (TyOverride _) dir) (MkPort (TyOverride _) dir) | (Yes ItIs) | IsOver | alt
       = Nothing


    validArgs (MkPort (TyVect s t) dir) (MkPort (TyVect s v) dir) | (Yes ItIs) | IsVect
      = Just (NoChange t v)

  validArgs port value | (No contra)
    = Nothing

public export
sizeOf : {n : Nat}
      -> (0 port  : SystemV Nil (PortTy (VectorTyDesc (W (S n) ItIsSucc) type) dir))
      -> (value : Value port)
      -> (vargs : Args port value)
               -> SystemV Nil (NatTy (S n))
sizeOf {n} port value vargs with (vargs)
  sizeOf {n = n} (MkPort (TyVect (W (S n) ItIsSucc) dtype) dir) (MkPort (TyVect (W (S n) ItIsSucc) dvalue) dir) vargs | (NoChange dtype dvalue)
    = MkNat (S n)
  sizeOf {n = n} (MkPort (TyOverride dtype) dir) (MkPort (TyOverride dvalue) dir) vargs | (Overridden dtype dvalue prf) with (prf)
    sizeOf {n = n} (MkPort (TyOverride (TyVect o datatype)) dir) (MkPort (TyOverride (TyVect o datatypev)) dir) vargs | (Overridden (TyVect o datatype) (TyVect o datatypev) prf) | ItIsVect with (o)
      sizeOf {n = n} (MkPort (TyOverride (TyVect o datatype)) dir) (MkPort (TyOverride (TyVect o datatypev)) dir) vargs | (Overridden (TyVect o datatype) (TyVect o datatypev) prf) | ItIsVect | (W k x)
        = NatOverride k


-- [ EOF ]
