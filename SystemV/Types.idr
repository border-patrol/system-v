||| A Meta-Type System for SystemV
|||
||| We provide a 'meta' type-system to provide intrinsic typing of terms in SystemV.
||| Certain terms in SystemV are typed using nominal types: Where they are defined matters.
||| We use the meta-type system to ensure that nominally typed values can be typed intrinsically against their nominal types.
module SystemV.Types

import SystemV.Utilities

%default total


||| Levels at which types and their types are defined in our type
||| universes.
public export
data Level = VALUE -- Describes a type that describes a value.
           | TYPE  -- Describes a type that describes a type.


||| The Universes in our setup: Data or things that contain data.
public export
data Universe = DATA Level -- Describes things that are data.
              | IDX  Level -- Describes things that contain data.


public export
data Direction = IN | OUT | INOUT

public export
data ValidDirCast : (l,r : Direction) -> Type where
  InsertEndpointIB : ValidDirCast IN  INOUT
  InsertEndpointOB : ValidDirCast OUT INOUT
  InsertEndpointXX : ValidDirCast a   a

public export
data ValidFlow : (l,r : Direction) -> Type where
  FlowOI : ValidFlow OUT   IN
  FlowBI : ValidFlow INOUT IN
  FlowOB : ValidFlow OUT   INOUT
  FlowBB : ValidFlow INOUT INOUT

||| Our types are meta types...
public export
data MTy : Universe -> Type where
  -- [ Data types ]

  -- Type def.
  TypeDefTy : MTy (DATA level) -> MTy (DATA level)

  -- Primitive Types
  BoolTyDesc : MTy (DATA TYPE)
  BoolTy     : MTy (DATA VALUE)

  LogicTyDesc : MTy (DATA TYPE)
  LogicTy     : MTy (DATA VALUE)

  VectorTyDesc : (n : Nat) -> MTy (DATA TYPE)  -> MTy (DATA TYPE)
  VectorTy     : (n : Nat) -> MTy (DATA VALUE) -> MTy (DATA VALUE)

  -- [ Function types ]
  FuncTy : MTy (IDX level) -> MTy (IDX level) -> MTy (IDX level)

  -- [ Structural Types ]

  -- Modules
  ModuleTyDesc : MTy (IDX TYPE)
  ModuleTy     : MTy (IDX VALUE)

  -- Channels
  ChanTy  : (type : MTy (DATA TYPE)) -> MTy (IDX TYPE)
  ChanVal : (type : MTy (DATA TYPE)) -> MTy (IDX VALUE)

  PortTy  : (type : MTy (DATA TYPE)) -> (dir : Direction) -> MTy (IDX TYPE)
  PortVal : (type : MTy (DATA TYPE)) -> (dir : Direction) -> MTy (IDX VALUE)

  ParamTy  : MTy (IDX TYPE)
  ParamVal : MTy (IDX VALUE)

  -- [ Misc ]
  UnitTy  : MTy (IDX TYPE)
  UnitVal : MTy (IDX VALUE)

public export
data EquivTypes : (typeA, typeB : MTy (DATA TYPE)) -> Type where
  Same : EquivTypes a a

public export
data ValidCast : (typeA, typeB : MTy (IDX VALUE))
              -> Type
  where
   CanCast : (castDir : ValidDirCast           dirA               dirB)
          -> (castTy  : EquivTypes         tyA                tyB)
                     -> ValidCast (PortVal tyA dirA) (PortVal tyB dirB)

||| A predicate to type check data types against values
public export
data TyCheckData : (type  : MTy (DATA TYPE))
                -> (value : MTy (DATA VALUE))
                -> Type
  where
    ChkDataBool   : TyCheckData BoolTyDesc  BoolTy
    ChkDataLogic  : TyCheckData LogicTyDesc LogicTy

    ChkDataVector : TyCheckData                 typeDesc              type
                 -> TyCheckData (VectorTyDesc s typeDesc) (VectorTy s type)

    ChkNewtype   : TyCheckData            innerType             innerValue
                -> TyCheckData (TypeDefTy innerType) (TypeDefTy innerValue)

||| A predicate to type check types against type formers.
public export
data TyCheck : (type  : MTy (IDX TYPE))
            -> (value : MTy (IDX VALUE))
            -> Type
  where
    ChkModule : TyCheck ModuleTyDesc ModuleTy
    ChkUnit   : TyCheck UnitTy       UnitVal

    ChkFunc : TyCheck         paramTy                   paramValue
           -> TyCheck                 returnTy                     returnValue
           -> TyCheck (FuncTy paramTy returnTy) (FuncTy paramValue returnValue)

    ChkChan  : TyCheck (ChanTy type) (ChanVal type)

    ChkPort : TyCheck (PortTy type dir) (PortVal type dir)

    ChkParam : TyCheck ParamTy ParamVal

||| A context is a list of types in different universes.
public export
Context : List Universe -> Type
Context = DList Universe MTy

public export
Contains : Context lvls -> MTy kind -> Type
Contains g ty = Elem Universe MTy ty g


-- --------------------------------------------------------------------- [ EOF ]
