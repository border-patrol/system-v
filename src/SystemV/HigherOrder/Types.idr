||| A Meta-Type System for SystemV
|||
||| We provide a 'meta' type-system to provide intrinsic typing of terms in SystemV.HigherOrder.
||| Certain terms in SystemV.HigherOrder.are typed using nominal types: Where they are defined matters.
||| We use the meta-type system to ensure that nominally typed values can be typed intrinsically against their nominal types.
module SystemV.HigherOrder.Types

import public Decidable.Equality
import public Data.Nat

import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import public Toolkit.Data.Whole

import public Toolkit.Data.List.DeBruijn
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem
import public Toolkit.Data.DList.DeBruijn

import public SystemV.Common.Types.Direction
import public SystemV.Common.Sliceable

import public SystemV.Core.Types.TYPE

import public SystemV.Core.Types.TYPE.Equality
import public SystemV.Core.Types.TYPE.Equiv
import public SystemV.Core.Types.TYPE.Cast

import public SystemV.HigherOrder.Types.Function

import public SystemV.Core.Types.TYPE.Check.Data
import public SystemV.Core.Types.TYPE.Check.Types

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
