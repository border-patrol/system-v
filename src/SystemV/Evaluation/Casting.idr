module SystemV.Evaluation.Casting

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms

import SystemV.Evaluation.Values

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

cast (CanCast castDir castTy) (Seq left right) (Seq x y)
  = Seq left $ cast (CanCast castDir castTy) right y

-- [ EOF ]
