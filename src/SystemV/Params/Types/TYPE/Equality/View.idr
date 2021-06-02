module SystemV.Params.Types.TYPE.Equality.View

import Data.Nat
import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Common.Types.Direction
import SystemV.Params.Types.TYPE

import  SystemV.Params.Types.TYPE.Equality.Error

%default total

public export
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

export
byIndex : {idxA, idxB : Universe}
       -> (a : TYPE idxA)
       -> (b : TYPE idxB)
       -> ByIndex a b
byIndex a b {idxA} {idxB} with (Universe.decEq idxA idxB)
  byIndex a b {idxA = idxB} {idxB = idxB} | (Yes Refl) = (IdxSame a b Refl)
  byIndex a b {idxA = idxA} {idxB = idxB} | (No contra) = (IdxDiff a b contra)


-- [ EOF ]
