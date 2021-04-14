||| A Meta-Type System for SystemV
|||
||| We provide a 'meta' type-system to provide intrinsic typing of terms in SystemV.Base.
||| Certain terms in SystemV.Base.are typed using nominal types: Where they are defined matters.
||| We use the meta-type system to ensure that nominally typed values can be typed intrinsically against their nominal types.
module SystemV.Base.Types

import public Decidable.Equality

import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Utilities

import public SystemV.Base.Types.Direction
import public SystemV.Base.Types.Gate

import public SystemV.Base.Types.TYPE

import public SystemV.Base.Types.TYPE.Equality
import public SystemV.Base.Types.TYPE.Equiv
import public SystemV.Base.Types.TYPE.Cast
import public SystemV.Base.Types.TYPE.Sliceable
import public SystemV.Base.Types.TYPE.Function

import public SystemV.Base.Types.TYPE.Check.Data
import public SystemV.Base.Types.TYPE.Check.Types

%default total

public export
Universes : Type
Universes = List Universe

||| A context is a list of types in different universes.
public export
Context : Universes -> Type
Context = DList Universe TYPE


public export
Contains : Context lvls -> TYPE kind -> Type
Contains g ty = Elem Universe TYPE ty g

-- [ EOF ]
