module SystemV.Common.Sliceable

import Data.Nat

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.Whole

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

-- [ EOF ]
