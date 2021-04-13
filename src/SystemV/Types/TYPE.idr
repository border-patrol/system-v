||| Types in SystemV.
|||
||| Types in SystemV are indexed over two levels:
|||
||| + TERM, that describes types that describe terms.
||| + TYPE, that describes types that describe types.
|||
module SystemV.Types.TYPE

import Data.Nat
import Decidable.Equality

import public Toolkit.Data.Whole
import Toolkit.Decidable.Equality.Indexed

import SystemV.Utilities
import public SystemV.Types.Direction

%default total

namespace Level


  ||| Levels at which types and their types are defined in our type
  ||| universes.
  public export
  data Level = TERM -- Describes a type that describes a value.
             | TYPE  -- Describes a type that describes a type.

  valueNotType : TERM = TYPE -> Void
  valueNotType Refl impossible

  export
  DecEq Level where
    decEq TERM TERM = Yes Refl
    decEq TERM TYPE = No valueNotType
    decEq TYPE TERM = No (negEqSym valueNotType)
    decEq TYPE TYPE = Yes Refl


||| The Universes in our setup: Data or things that contain data.
public export
data Universe = DATA Level -- Describes things that are data.
              | IDX  Level -- Describes things that contain data.

namespace Universe

  dataNotSameLevel : (contra : x = y -> Void)
                  -> (prf    : DATA x = DATA y)
                            -> Void
  dataNotSameLevel contra Refl = contra Refl

  dataIdxNotEq : DATA x = IDX y -> Void
  dataIdxNotEq Refl impossible

  idxNotSameLevel : (contra : x = y -> Void)
                 -> (prf    : IDX x = IDX y)
                           -> Void
  idxNotSameLevel contra Refl = contra Refl


  export
  DecEq Universe where
    decEq (DATA x) (DATA y) with (decEq x y)
      decEq (DATA x) (DATA x) | (Yes Refl) = Yes Refl
      decEq (DATA x) (DATA y) | (No contra) = No (dataNotSameLevel contra)

    decEq (DATA x) (IDX y) = No dataIdxNotEq

    decEq (IDX x) (DATA y) = No (negEqSym dataIdxNotEq)
    decEq (IDX x) (IDX y) with (decEq x y)
      decEq (IDX x) (IDX x) | (Yes Refl) = Yes Refl
      decEq (IDX x) (IDX y) | (No contra) = No (idxNotSameLevel contra)


||| Our types are meta types...
public export
data TYPE : Universe -> Type where
  -- [ Data types ]

  -- Type def.
  TypeDefTy : TYPE (DATA level) -> TYPE (DATA level)

  -- Primitive Types
  BoolTyDesc : TYPE (DATA TYPE)
  BoolTy     : TYPE (DATA TERM)

  LogicTyDesc : TYPE (DATA TYPE)
  LogicTy     : TYPE (DATA TERM)

  VectorTyDesc : (size : Whole)
              -> (type : TYPE (DATA TYPE))
                      -> TYPE (DATA TYPE)

  VectorTy : (size : Whole)
          -> (type : TYPE (DATA TERM))
                  -> TYPE (DATA TERM)

  -- [ Function types ]
  FuncTy : (param  : TYPE (IDX level))
        -> (return : TYPE (IDX level))
                  -> TYPE (IDX level)

  -- [ Structural Types ]

  -- Modules
  ModuleTyDesc : TYPE (IDX TYPE)
  ModuleTy     : TYPE (IDX TERM)

  -- Channels
  ChanTyDesc : (type : TYPE (DATA TYPE))
                    -> TYPE (IDX TYPE)

  ChanTy     : (type : TYPE (DATA TYPE))
                    -> TYPE (IDX TERM)

  PortTyDesc  : (type : TYPE (DATA TYPE))
             -> (dir  : Direction)
                     -> TYPE (IDX TYPE)

  PortTy : (type : TYPE (DATA TYPE))
        -> (dir  : Direction)
                -> TYPE (IDX TERM)

  -- [ Misc ]
  UnitTyDesc : TYPE (IDX TYPE)
  UnitTy     : TYPE (IDX TERM)

  NatTyDesc : Nat -> TYPE (IDX TYPE)
  NatTy     : Nat -> TYPE (IDX TERM)


-- --------------------------------------------------------------------- [ EOF ]
