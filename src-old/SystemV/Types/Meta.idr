module SystemV.Types.Meta

import Data.Nat
import Decidable.Equality

import public Toolkit.Data.Whole
import Toolkit.Decidable.Equality.Indexed

import SystemV.Utilities
import SystemV.Types.Direction

%default total

||| Levels at which types and their types are defined in our type
||| universes.
public export
data Level = VALUE -- Describes a type that describes a value.
           | TYPE  -- Describes a type that describes a type.


namespace Level

  valueNotType : VALUE = TYPE -> Void
  valueNotType Refl impossible


  export
  DecEq Level where
    decEq VALUE VALUE = Yes Refl
    decEq VALUE TYPE = No valueNotType
    decEq TYPE VALUE = No (negEqSym valueNotType)
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
data Meta : Universe -> Type where
  -- [ Data types ]

  -- Type def.
  TypeDefTy : Meta (DATA level) -> Meta (DATA level)

  -- Primitive Types
  BoolTyDesc : Meta (DATA TYPE)
  BoolTy     : Meta (DATA VALUE)

  LogicTyDesc : Meta (DATA TYPE)
  LogicTy     : Meta (DATA VALUE)

  VectorTyDesc : (n : Whole) -> Meta (DATA TYPE)  -> Meta (DATA TYPE)
  VectorTy     : (n : Whole) -> Meta (DATA VALUE) -> Meta (DATA VALUE)

  -- [ Function types ]
  FuncTy : Meta (IDX level) -> Meta (IDX level) -> Meta (IDX level)

  -- [ Structural Types ]

  -- Modules
  ModuleTyDesc : Meta (IDX TYPE)
  ModuleVal     : Meta (IDX VALUE)

  -- Channels
  ChanTy  : (type : Meta (DATA TYPE)) -> Meta (IDX TYPE)
  ChanVal : (type : Meta (DATA TYPE)) -> Meta (IDX VALUE)

  PortTy  : (type : Meta (DATA TYPE)) -> (dir : Direction) -> Meta (IDX TYPE)
  PortVal : (type : Meta (DATA TYPE)) -> (dir : Direction) -> Meta (IDX VALUE)

  ParamTy  : Meta (IDX TYPE)
  ParamVal : Meta (IDX VALUE)

  -- [ Misc ]
  UnitTy  : Meta (IDX TYPE)
  UnitVal : Meta (IDX VALUE)

public export
MTy : Universe -> Type
MTy = Meta

-- --------------------------------------------------------------------- [ EOF ]
