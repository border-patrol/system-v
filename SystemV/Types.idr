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
  LogicTyDesc : MTy (DATA TYPE)
  LogicTy     : MTy (DATA VALUE)


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

  ParamTy  : (type : MTy (DATA TYPE)) -> MTy (IDX TYPE)
  ParamVal : (type : MTy (DATA TYPE)) -> MTy (IDX VALUE)

  -- [ Misc ]
  UnitTy  : MTy (IDX TYPE)
  UnitVal : MTy (IDX VALUE)

||| A predicate to type check data types against values
public export
data TyCheckData : (type  : MTy (DATA TYPE))
                -> (value : MTy (DATA VALUE))
                -> Type
  where
    ChkDataLogic : TyCheckData LogicTyDesc LogicTy

    ChkNewtype   : TyCheckData            innerType             innerValue
                -> TyCheckData (TypeDefTy innerType) (TypeDefTy innerValue)

||| A predicate to type check types against type formers.
public export
data TyCheck : (type  : MTy (IDX TYPE))
            -> (value : MTy (IDX VALUE))
            -> Type
  where
    ChkModule : TyCheck ModuleTyDesc ModuleTy

    ChkFunc : TyCheck         paramTy                   paramValue
           -> TyCheck                 returnTy                     returnValue
           -> TyCheck (FuncTy paramTy returnTy) (FuncTy paramValue returnValue)

    ChkChan  : TyCheck (ChanTy type) (ChanVal type)

    ChkPort : TyCheck (PortTy type dir) (PortVal type dir)

    ChkParam : TyCheck (ParamTy type) (ParamVal type)

--||| Valid Connection.
--public export
--data ValidConn : (l : MTy (IDX VALUE))
--              -> (r : MTy (IDX VALUE))
--                   -> Type
--  where
--    ConnPP : ValidFlow l r -> ValidConn (PortVal type l) (PortVal type r)
--
--    ConnPoC : ValidConn (PortVal type OUT)   (ChanVal type)
--    ConnPbC : ValidConn (PortVal type INOUT) (ChanVal type)
--    ConnCPi : ValidConn (ChanVal type)       (PortVal type IN)
--    ConnCPb : ValidConn (ChanVal type)       (PortVal type INOUT)

--||| Valid Application
--public export
--data ValidApp : (l : MTy (IDX VALUE))
--             -> (r : MTy (IDX VALUE))
--                  -> Type
--  where
--    AppParam : ValidApp (ParamVal type) (ParamVal type)
--    AppWire  : ValidConn l r -> ValidApp l r

||| A context is a list of types in different universes.
public export
Context : List Universe -> Type
Context = DList Universe MTy

public export
Contains : Context lvls -> MTy kind -> Type
Contains g ty = Elem Universe MTy ty g
