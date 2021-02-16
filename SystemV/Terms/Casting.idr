module SystemV.Terms.Casting

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms
import SystemV.Values

%default total

public export
castDir : {dirTo : Direction}
       -> (prf   : ValidDirCast dirFrom dirTo)
                -> Direction
castDir {dirTo} _ = dirTo

public export
castTy : (prf : EquivTypes fromTy toTy)
      -> (tm  : SystemV ctxt fromTy)
      -> (val : Value tm)
             -> SystemV ctxt toTy
castTy Same tm val = tm

public export
cast : {fromPort, toPort : MTy (IDX VALUE)}
    -> (prf   : ValidCast fromPort toPort)
    -> (from  : SystemV ctxt fromPort)
    -> (value : Value from)
             -> SystemV ctxt toPort
cast (CanCast castDir' castTy') (MkPort type dirA) (MkPort x dirA)
  = MkPort (castTy castTy' type x) (castDir castDir')



-- --------------------------------------------------------------------- [ EOF ]
