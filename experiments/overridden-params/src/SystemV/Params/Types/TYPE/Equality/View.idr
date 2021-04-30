module SystemV.Params.Types.TYPE.Equality.View

import SystemV.Params.Types.TYPE

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
