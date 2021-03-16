module SystemV.Types.Meta.Sliceable

import Data.Nat

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

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
  data Error = InvalidType (Meta u)
             | BadRange Nat Nat
             | BadBound (Nat,Nat) Nat
             | BadTypeDef Bound.Error

  public export
  data ValidBound : (type : Meta (DATA TYPE))
                 -> (alpha,omega : Nat)
                 -> Type
    where
      ArrayBound : (prfB : LT alpha omega)
                -> (prfL : LTE omega s)
                        -> ValidBound (VectorTyDesc s type) alpha omega

  notBoundableB : ValidBound (BoolTyDesc)  a o -> Void
  notBoundableB (ArrayBound prfB prfL) impossible

  notBoundableL : ValidBound (LogicTyDesc) a o -> Void
  notBoundableL (ArrayBound prfB prfL) impossible

  notBoundableT : ValidBound (TypeDefTy type) a o -> Void
  notBoundableT (ArrayBound prfB prfL) impossible

  badBound : (LT a o -> Void)
          -> ValidBound (VectorTyDesc n type) a o
          -> Void
  badBound f (ArrayBound prfB prfL) = f prfB

  badRange : (LTE o n -> Void)
          -> ValidBound (VectorTyDesc n type) a o
          -> Void
  badRange f (ArrayBound prfB prfL) = f prfL

  export
  validBound : (type : Meta (DATA TYPE))
            -> (a,o  : Nat)
                    -> DecInfo Bound.Error (ValidBound type a o)
  validBound type a o with (type)
    validBound type a o | BoolTyDesc
      = No (InvalidType type) notBoundableB
    validBound type a o | LogicTyDesc
      = No (InvalidType type) notBoundableL
    validBound type a o | (TypeDefTy x)
      = No (InvalidType type) notBoundableT

    validBound type a o | (VectorTyDesc n x) with (isLTE (S a) o)
      validBound type a o | (VectorTyDesc n x) | (Yes prf) with (isLTE o n)
        validBound type a o | (VectorTyDesc n x) | (Yes prf) | (Yes y)
          = Yes (ArrayBound prf y)

        validBound type a o | (VectorTyDesc n x) | (Yes prf) | (No contra)
        = No (BadBound (a,o) n) (badRange contra)

      validBound type a o | (VectorTyDesc n x) | (No contra)
        = No (BadRange a o) (badBound contra)

namespace Slicing

  public export
  data CanSlice : (level       : Universe)
               -> (input       : Meta level)
               -> (alpha,omega : Nat)
               -> (out         : Meta level)
                              -> Type
    where
      YesCanSlice : (prfS : Sliceable (DATA TYPE)
                                      (VectorTyDesc s type))
                 -> (prfB : ValidBound (VectorTyDesc s type) alpha omega)
                         -> CanSlice (DATA TYPE)
                                     (VectorTyDesc s type)
                                     alpha
                                     omega
                                     (VectorTyDesc (minus omega alpha) type)


  invalidSlice : (contra : Sliceable level type -> Void)
              -> (out    : Meta level ** CanSlice level type alpha omega out)
                        -> Void
  invalidSlice contra (MkDPair (VectorTyDesc (minus omega alpha) type) (YesCanSlice prfS prfB)) = contra prfS

  isType : (out : Meta (IDX _) ** CanSlice (IDX _) type alpha omega out) -> Void
  isType (MkDPair _ (YesCanSlice prfS prfB)) impossible

  isValue : (out : Meta (DATA VALUE) ** CanSlice (DATA VALUE) type alpha omega out) -> Void
  isValue (MkDPair _ (YesCanSlice prfS prfB)) impossible

  invalidBound : (contra : ValidBound type alpha omega -> Void)
              -> (out    : Meta (DATA TYPE) ** CanSlice (DATA TYPE) type alpha omega out)
                        -> Void
  invalidBound contra (MkDPair (VectorTyDesc (minus omega alpha) type) (YesCanSlice prfS prfB)) = contra prfB


  public export
  data Error = InvalidBound Bound.Error
             | InvalidType (Meta u)
             | InvalidSlice (Sliceable.Error)

  export
  canSlice : {level       : Universe}
          -> (type        : Meta level)
          -> (alpha,omega : Nat)
                         -> DecInfo Slicing.Error
                                    (out ** CanSlice level type alpha omega out)
  canSlice type alpha omega {level = (IDX _)}
    = No (InvalidType type) isType

  canSlice type alpha omega {level = (DATA VALUE)}
    = No (InvalidType type) isValue

  canSlice type alpha omega {level = (DATA TYPE)} with (sliceable type)
    canSlice (VectorTyDesc n innertype) alpha omega {level = (DATA TYPE)} | (Yes ArraysAre) with (validBound (VectorTyDesc n innertype) alpha omega)
      canSlice (VectorTyDesc n innertype) alpha omega {level = (DATA TYPE)} | (Yes ArraysAre) | (Yes prfWhy)
        = Yes (MkDPair (VectorTyDesc (minus omega alpha) innertype) (YesCanSlice ArraysAre prfWhy))

      canSlice (VectorTyDesc n innertype) alpha omega {level = (DATA TYPE)} | (Yes ArraysAre) | (No msgWhyNot prfWhyNot)
        = No (InvalidBound msgWhyNot) (invalidBound prfWhyNot)

    canSlice type alpha omega {level = (DATA TYPE)} | (No msgWhyNot prfWhyNot)
      = No (InvalidSlice msgWhyNot) (invalidSlice prfWhyNot)

-- --------------------------------------------------------------------- [ EOF ]
