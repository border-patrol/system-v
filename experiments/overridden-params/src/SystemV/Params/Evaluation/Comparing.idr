module SystemV.Params.Evaluation.Comparing

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden
import SystemV.Params.Evaluation.Values.Predicates

%default total

public export
data Args : (leftTm   : SystemV Nil (NatTy l))
         -> (leftVal  : Value leftTm)
         -> (rightTm  : SystemV Nil (NatTy r))
         -> (rightVal : Value rightTm)
                     -> Type

  where
    BothNats : Args (MkNat l) MkNat
                    (MkNat r) MkNat

    OverLeft : Args (NatOverride k) NatOverride
                    (MkNat r)       MkNat

    OverRight : Args (MkNat l)       MkNat
                     (NatOverride s) NatOverride

    BothOver : Args (NatOverride k) NatOverride
                    (NatOverride s) NatOverride

export
validArgs : (leftTm   : SystemV Nil (NatTy l))
         -> (leftVal  : Value leftTm)
         -> (rightTm  : SystemV Nil (NatTy r))
         -> (rightVal : Value rightTm)
                     -> Maybe (Args leftTm  leftVal
                                    rightTm rightVal)
validArgs lT lV rT rV with (isNat lV)
  validArgs (MkNat l) MkNat rT rV | (Yes ItIsPure) with (isNat rV)
    validArgs (MkNat l) MkNat (MkNat r) MkNat | (Yes ItIsPure) | (Yes ItIsPure)
      = Just BothNats

    validArgs (MkNat l) MkNat (NatOverride s) NatOverride | (Yes ItIsPure) | (Yes ItIsOver)
      = Just OverRight

    validArgs (MkNat l) MkNat rT rV | (Yes ItIsPure) | (No contra)
      = Nothing

  validArgs (NatOverride m) NatOverride rT rV | (Yes ItIsOver) with (isNat rV)
    validArgs (NatOverride k) NatOverride (MkNat r) MkNat | (Yes ItIsOver) | (Yes ItIsPure)
      = Just OverLeft

    validArgs (NatOverride k) NatOverride (NatOverride s) NatOverride | (Yes ItIsOver) | (Yes ItIsOver)
      = Just BothOver

    validArgs (NatOverride k) NatOverride rT rV | (Yes ItIsOver) | (No contra)
      = Nothing

  validArgs lT lV rT rV | (No contra)
    = Nothing

public export
compare : (op : Nat -> Nat -> Bool)
       -> (leftTm   : SystemV Nil (NatTy l))
       -> (leftVal  : Value leftTm)
       -> (rightTm  : SystemV Nil (NatTy r))
       -> (rightVal : Value rightTm)
       -> (vargs    : Args leftTm  leftVal
                           rightTm rightVal)
                   -> SystemV Nil BoolTy
compare op lT lV rT rV vargs with (vargs)
  compare op (MkNat l) MkNat (MkNat r) MkNat vargs | BothNats
    = B (op l r)
  compare op (NatOverride k) NatOverride (MkNat r) MkNat vargs | OverLeft
    = B (op k r)
  compare op (MkNat l) MkNat (NatOverride s) NatOverride vargs | OverRight
    = B (op l s)
  compare op (NatOverride k) NatOverride (NatOverride s) NatOverride vargs | BothOver
    = B (op k s)
