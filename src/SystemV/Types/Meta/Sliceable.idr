module SystemV.Types.Meta.Sliceable

import Data.Nat

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import Toolkit.Data.Whole

import SystemV.Utilities
import SystemV.Types.Direction
import SystemV.Types.Meta

%default total

public export
data Sliceable : (level : Universe)
              -> (type  : Meta level)
                       -> Type
  where
    ArraysAre   : Sliceable (DATA TYPE) (VectorTyDesc n innertype)

isDataValue : Sliceable (DATA VALUE) type -> Void
isDataValue ArraysAre impossible

isTypeType : Sliceable (IDX TYPE) type -> Void
isTypeType ArraysAre impossible

isTypeValue : Sliceable (IDX VALUE) type -> Void
isTypeValue ArraysAre impossible

isBool : Sliceable (DATA TYPE) BoolTyDesc -> Void
isBool ArraysAre impossible

isLogic : Sliceable (DATA TYPE) LogicTyDesc -> Void
isLogic ArraysAre impossible

isTypeDef : Sliceable (DATA TYPE) (TypeDefTy type) -> Void
isTypeDef ArraysAre impossible

public export
data Error : Type where
  CannotSlice : Meta u -> Error

export
sliceable : {level : Universe}
         -> (type  : Meta level)
                  -> DecInfo Sliceable.Error (Sliceable level type)
sliceable type {level} with (level)
  sliceable type {level = level} | (DATA VALUE)
    = No (CannotSlice type) isDataValue

  sliceable type {level = level} | (IDX VALUE)
    = No (CannotSlice type) isTypeValue

  sliceable type {level = level} | (IDX TYPE)
    = No (CannotSlice type) isTypeType

  sliceable type {level = level} | (DATA TYPE) with (type)
    sliceable type {level = level} | (DATA TYPE) | (TypeDefTy x)
      = No (CannotSlice type) isTypeDef

    sliceable type {level = level} | (DATA TYPE) | BoolTyDesc
      = No (CannotSlice type) isBool

    sliceable type {level = level} | (DATA TYPE) | LogicTyDesc
      = No (CannotSlice type) isLogic

    sliceable type {level = level} | (DATA TYPE) | (VectorTyDesc n x) = Yes ArraysAre

namespace Bound


  public export
  data ValidBound : (type : Meta (DATA TYPE))
                 -> (alpha : Nat)
                 -> (omega : Whole)
                 -> Type
    where
      ArrayBound : (prfU : LTE Z     alpha)             -- 0     <= alpha
                -> (prfB : LTE   (S  alpha) omega)      -- alpha <  omega]
                -> (prfL : LT               omega  s)   -- omega <  s
                        -> ValidBound (VectorTyDesc s type) alpha omega

  notBoundableB : ValidBound (BoolTyDesc)  a o -> Void
  notBoundableB (ArrayBound prfU prfB prfL) impossible

  notBoundableL : ValidBound (LogicTyDesc) a o -> Void
  notBoundableL (ArrayBound prfU prfB prfL) impossible

  notBoundableT : ValidBound (TypeDefTy type) a o -> Void
  notBoundableT (ArrayBound prfU prfB prfL) impossible

  badAlpha : (contra : LTE Z alpha -> Void)
          -> ValidBound (VectorTyDesc n type) alpha omega
          -> Void
  badAlpha contra (ArrayBound prfU prfB prfL) = contra prfU

  badBound : (LTE (S a) o -> Void)
          -> ValidBound (VectorTyDesc n type) a o
          -> Void
  badBound f (ArrayBound prfU prfB prfL) = f prfB

  badRange : (LT o n -> Void)
          -> ValidBound (VectorTyDesc n type) a o
          -> Void
  badRange f (ArrayBound prfU prfB prfL) = f prfL

  public export
  data Error = InvalidType (Meta u)
             | BadRange Nat Whole
             | BadBound (Nat,Whole) Whole
             | IndexStartsZero Nat

  export
  validBound : (type : Meta (DATA TYPE))
            -> (a    : Nat)
            -> (o    : Whole)
                    -> DecInfo Bound.Error (ValidBound type a o)
  validBound type a o with (type)
    validBound type a o | BoolTyDesc
      = No (InvalidType type) notBoundableB
    validBound type a o | LogicTyDesc
      = No (InvalidType type) notBoundableL
    validBound type a o | (TypeDefTy x)
      = No (InvalidType type) notBoundableT
    validBound type a o | (VectorTyDesc n x) with (isLTE Z a)
      validBound type a o | (VectorTyDesc n x) | (Yes prfU) with (isLTE (S a) o)
        validBound type a o | (VectorTyDesc n x) | (Yes prfU) | (Yes prfR) with (isLT o n)
          validBound type a o | (VectorTyDesc n x) | (Yes prfU) | (Yes prfR) | (Yes prfL)
            = Yes (ArrayBound prfU prfR prfL)
          validBound type a o | (VectorTyDesc n x) | (Yes prfU) | (Yes prfR) | (No contra)
            = No (BadBound (a,o) n) (badRange contra)

        validBound type a o | (VectorTyDesc n x) | (Yes prfU) | (No contra)
          = No (BadRange a o) (badBound contra)

      validBound type a o | (VectorTyDesc n x) | (No contra)
        = No (IndexStartsZero a) (badAlpha contra)

namespace Slicing

  public export
  minus : (omega : Whole)
       -> (alpha : Nat)
       -> (prf   : LTE (S alpha) omega)
       -> Whole
  minus (W (S omega) ItIsSucc) 0 prf = W (S (S omega)) ItIsSucc
  minus (W (S right) ItIsSucc) (S k) (IsLTE (LTESucc x)) = W (S (minus right (S k))) ItIsSucc

  public export
  sizeFromBound : (alpha : Nat)
               -> (omega : Whole)
               -> (prf : ValidBound (VectorTyDesc s type) alpha omega)
               -> Whole
  sizeFromBound alpha omega (ArrayBound prfU prfB prfL) = minus omega alpha prfB

  public export
  data CanSlice : (level : Universe)
               -> (input : Meta level)
               -> (alpha : Nat)
               -> (omega : Whole)
               -> (out   : Meta level)
                        -> Type
    where
      YesCanSlice : (prfS : Sliceable (DATA TYPE)
                                      (VectorTyDesc s type))
                 -> (prfB : ValidBound (VectorTyDesc s type) alpha omega)
                         -> CanSlice (DATA TYPE)
                                     (VectorTyDesc s type)
                                     alpha
                                     omega
                                     (VectorTyDesc (sizeFromBound alpha omega prfB) type)



  invalidSlice : (contra : Sliceable level type -> Void)
              -> (out    : Meta level ** CanSlice level type alpha omega out)
                        -> Void
  invalidSlice contra (MkDPair (VectorTyDesc (sizeFromBound alpha omega prfB) type) (YesCanSlice prfS prfB)) = contra prfS


  isType : (out : Meta (IDX _) ** CanSlice (IDX _) type alpha omega out) -> Void
  isType (MkDPair _ (YesCanSlice prfS prfB)) impossible

  isValue : (out : Meta (DATA VALUE) ** CanSlice (DATA VALUE) type alpha omega out) -> Void
  isValue (MkDPair _ (YesCanSlice prfS prfB)) impossible

  invalidBound : (contra : ValidBound type alpha omega -> Void)
              -> (out    : Meta (DATA TYPE) ** CanSlice (DATA TYPE) type alpha omega out)
                        -> Void
  invalidBound contra (MkDPair (VectorTyDesc (sizeFromBound alpha omega prfB) type) (YesCanSlice prfS prfB)) = contra prfB



  public export
  data Error = InvalidBound Bound.Error
             | InvalidType (Meta u)
             | InvalidSlice (Sliceable.Error)

  export
  canSlice : {level : Universe}
          -> (type  : Meta level)
          -> (alpha : Nat)
          -> (omega : Whole)
                   -> DecInfo Slicing.Error
                              (out ** CanSlice level type alpha omega out)
  canSlice type alpha omega {level = (IDX _)}
    = No (InvalidType type) isType

  canSlice type alpha omega {level = (DATA VALUE)}
    = No (InvalidType type) isValue

  canSlice type alpha omega {level = (DATA TYPE)} with (sliceable type)
    canSlice (VectorTyDesc n innertype) alpha omega {level = (DATA TYPE)} | (Yes ArraysAre) with (validBound (VectorTyDesc n innertype) alpha omega)
      canSlice (VectorTyDesc n innertype) alpha omega {level = (DATA TYPE)} | (Yes ArraysAre) | (Yes prfWhy)
          = Yes (VectorTyDesc (sizeFromBound alpha omega prfWhy) innertype ** YesCanSlice ArraysAre prfWhy)

      canSlice (VectorTyDesc n innertype) alpha omega {level = (DATA TYPE)} | (Yes ArraysAre) | (No msgWhyNot prfWhyNot)
        = No (InvalidBound msgWhyNot) (invalidBound prfWhyNot)

    canSlice type alpha omega {level = (DATA TYPE)} | (No msgWhyNot prfWhyNot)
      = No (InvalidSlice msgWhyNot) (invalidSlice prfWhyNot)

-- --------------------------------------------------------------------- [ EOF ]
