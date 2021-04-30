module SystemV.Params.Evaluation.Arith

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden
import SystemV.Params.Evaluation.Values.Predicates

import SystemV.Params.Evaluation.Comparing

%default total

public export
data Args : (leftTm   : SystemV Nil (NatTy l))
         -> (leftVal  : Value leftTm)
         -> (rightTm  : SystemV Nil (NatTy r))
         -> (rightVal : Value rightTm)
                     -> Type


public export
data Args : (op       : Nat -> Nat -> Nat)
         -> (leftTm   : SystemV Nil (NatTy l))
         -> (leftVal  : Value leftTm)
         -> (rightTm  : SystemV Nil (NatTy r))
         -> (rightVal : Value rightTm)
                     -> Type
  where
    NotDiv : Args lt lv rt rv
          -> Arith.Args op lt lv rt
