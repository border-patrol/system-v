module SystemV.HigherOrder.Evaluation.Casting

import SystemV.Common.Utilities
import SystemV.HigherOrder.Types
import SystemV.HigherOrder.Terms

import SystemV.HigherOrder.Values

%default total

public export
castDir : {dirTo : Direction}
       -> (prf   : ValidDirCast dirFrom dirTo)
                -> Direction
castDir {dirTo} _ = dirTo

public export
castTy : {fromTy, toTy : TYPE (DATA TYPE)}

      -> (prf : EquivTypes fromTy toTy)
      -> (tm  : SystemV ctxt fromTy)
      -> (val : Value tm)
             -> SystemV ctxt toTy
castTy {fromTy = fromTy} {toTy = fromTy} (Same (Same Refl Refl)) tm val = tm


public export
cast : {fromPort, toPort : TYPE (IDX TERM)}
    -> (prf   : ValidCast fromPort toPort)
    -> (from  : SystemV ctxt fromPort)
    -> (value : Value from)
             -> SystemV ctxt toPort
cast (CanCast castDir' castTy') (MkPort type dirA) (MkPort x dirA)
  = MkPort (castTy castTy' type x)
           (castDir castDir')
cast (CanCast _ _) (Seq _ _ IsUnit) (Seq _ _) impossible
cast (CanCast _ _) (Seq _ _ IsMod) (Seq _ _) impossible

-- [ EOF ]
