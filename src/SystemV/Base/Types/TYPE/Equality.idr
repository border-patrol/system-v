module SystemV.Base.Types.TYPE.Equality

import        Data.Nat
import        Decidable.Equality

import        Toolkit.Decidable.Informative
import        Toolkit.Decidable.Equality.Indexed
import        Toolkit.Data.Whole

import        SystemV.Common.Utilities
import        SystemV.Base.Types.Direction
import        SystemV.Base.Types.TYPE

import public SystemV.Base.Types.TYPE.Equality.Error

import public SystemV.Base.Types.TYPE.Equality.DataTypes
import public SystemV.Base.Types.TYPE.Equality.DataTerms

import public SystemV.Base.Types.TYPE.Equality.TypeTypes
import public SystemV.Base.Types.TYPE.Equality.TypeTerms

%default total


data ByIndex : {idxA,idxB : Universe}
            -> (a   : TYPE idxA)
            -> (b   : TYPE idxB)
                   -> Type
  where
    IdxSame : {idxA,idxB  : Universe}
           -> (a          : TYPE idxA)
           -> (b          : TYPE idxB)
           -> (prf        : idxA === idxB)
                         -> ByIndex a b

    IdxDiff : {idxA, idxB : Universe}
           -> (a : TYPE idxA)
           -> (b : TYPE idxB)
           -> (prf : Not (idxA === idxB))
                  -> ByIndex a b

byIndex : {idxA, idxB : Universe}
       -> (a : TYPE idxA)
       -> (b : TYPE idxB)
       -> ByIndex a b
byIndex a b {idxA} {idxB} with (decEq idxA idxB)
  byIndex a b {idxA = idxB} {idxB = idxB} | (Yes Refl) = (IdxSame a b Refl)
  byIndex a b {idxA = idxA} {idxB = idxB} | (No contra) = (IdxDiff a b contra)

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
    decEq a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (IDX TERM)
      = TypeTerms.decEq a b
    decEq a b {aidx = bidx} {bidx = bidx} | (IdxSame a b Refl) | (IDX TYPE)
      = TypeTypes.decEq a b
  decEq a b {aidx = aidx} {bidx = bidx} | (IdxDiff a b contra)
    = No (KindMismatch aidx bidx) (indexAreSame contra)


-- --------------------------------------------------------------------- [ EOF ]
