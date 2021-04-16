module SystemV.Params.Types.TYPE.Sliceable

import Data.Nat

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.Whole

import SystemV.Common.Utilities

import SystemV.Common.Types.Direction

import SystemV.Params.Types.TYPE

%default total

public export
data ValidBound : (alpha : Nat)
               -> (omega : Nat)
               -> (size  : Whole)
               -> Type
  where
    ArrayBound : (prfU : LTE Z     alpha)               -- 0     <= alpha
              -> (prfB : LTE   (S  alpha)    omega)     -- alpha <  omega
              -> (prfL : LTE              (S omega)  s)  -- omega <  s
                      -> ValidBound alpha omega s

badAlpha : (contra : LTE Z alpha -> Void)
        -> ValidBound alpha omega s
        -> Void
badAlpha contra (ArrayBound prfU prfB prfL) = contra prfU

badBound : (LTE (S a) o -> Void)
        -> ValidBound a o s
        -> Void
badBound f (ArrayBound prfU prfB prfL) = f prfB

badOS : (LTE (S o) s -> Void) -> ValidBound a o s -> Void
badOS f (ArrayBound prfU prfB prfL) = f prfL

public export
data Error = BadBound Nat Nat
           | IndexStartsZero Nat
           | IndexToBig Nat

export
validBound : (a : Nat)
          -> (o : Nat)
          -> (s : Whole)
               -> DecInfo Sliceable.Error (ValidBound a o s)
validBound a o s with (isLTE Z a)
  validBound a o s | (Yes LTEZero) with (isLTE (S a) o)
    validBound a o s | (Yes LTEZero) | (Yes prfB) with (isLTE (S o) s)
      validBound a o s | (Yes LTEZero) | (Yes prfB) | (Yes prfL)
        = Yes (ArrayBound LTEZero prfB prfL)

      validBound a o s | (Yes LTEZero) | (Yes prfB) | (No contra)
        = No (IndexToBig o) (badOS contra)

    validBound a o s | (Yes LTEZero) | (No contra)
      = No (BadBound a o) (badBound contra)

  validBound a o s | (No contra)
    = No (IndexStartsZero a) (badAlpha contra)

public export
minus : (s : Whole)
     -> (o   : Nat)
     -> (a   : Nat)
     -> (prf : ValidBound a o s)
            -> Whole
minus s o a prf with (prf)
  minus s o a prf | (ArrayBound prfU prfB prfL) with (prfB)
    minus s (S right) Z prf | (ArrayBound prfU prfB prfL) | (LTESucc x)
      = W (S (S right)) ItIsSucc

    minus s (S right) (S k) prf | (ArrayBound prfU prfB prfL) | (LTESucc x)
      = W (S (minus (S right) (S k))) ItIsSucc

--minus s o Z prf = W (S o) ItIsSucc
--
--minus _ 0 (S _) (ArrayBound _ LTEZero _) impossible
--minus _ 0 (S _) (ArrayBound _ (LTESucc x) _) impossible
--
--minus s (S j) (S k) prf = W (S (minus (S j) (S k))) ItIsSucc

--minus (W (S n) ItIsSucc) o a (ArrayBound prfU prfB prfL) with (prfU)
--  minus (W (S n) ItIsSucc) (S 0) Z (ArrayBound prfU (LTESucc x) (IsLTE (LTESucc y))) | LTEZero
--    = W (S (S Z)) ItIsSucc
--
--  minus (W (S n) ItIsSucc) (S (S k)) Z (ArrayBound prfU (LTESucc x) (IsLTE (LTESucc y))) | LTEZero
--    = W ?minus_rhs_3_rhs_7
--
--  minus (W (S n) ItIsSucc) (S right) (S k) (ArrayBound prfU (LTESucc x) prfL) | LTEZero
--    = W (S (minus right (S k))) ItIsSucc

--minus (W (S n) ItIsSucc) o a (ArrayBound LTEZero prfB (IsLTE prf)) with (prfB)
--  minus (W (S n) ItIsSucc) (S right) Z (ArrayBound LTEZero prfB (IsLTE prf)) | (LTESucc LTEZero) = ?rhs_1
--  --  = W (S right) ItIsSucc
--  minus (W (S n) ItIsSucc) (S right) (S k) (ArrayBound LTEZero (LTESucc y) (IsLTE prf)) | (LTESucc x)
--    = W (S (minus right (S k))) ItIsSucc
--


-- [ EOF ]
