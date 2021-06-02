module SystemV.Params.Types.TYPE.Equality

import        Data.Nat
import        Decidable.Equality

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed
import        Toolkit.Data.Whole

import        SystemV.Common.Types.Direction
import        SystemV.Params.Types.TYPE

import public SystemV.Params.Types.TYPE.Equality.Error
import        SystemV.Params.Types.TYPE.Equality.View
import        SystemV.Params.Types.TYPE.Equality.DataTypes
import        SystemV.Params.Types.TYPE.Equality.DataTerms

import public SystemV.Params.Types.TYPE.Equality.Types

%default total

export
decEq : {aidx,bidx : Universe}
     -> (a         : TYPE aidx)
     -> (b         : TYPE bidx)
                       -> DecInfo Equality.Error (Equals Universe TYPE a b)
decEq a b {aidx} {bidx} with (byIndex a b)
  decEq a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) with (bidx)
    decEq a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (DATA TERM)
      = DataTerms.decEq a b
    decEq a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (DATA TYPE)
      = DataTypes.decEq a b
    decEq a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (IDX _)
      = Types.decEq a b
  decEq a b {aidx = aidx} {bidx = bidx} | (IdxDiff a b contra)
    = No (KindMismatch aidx bidx) (indexAreSame contra)


-- --------------------------------------------------------------------- [ EOF ]
