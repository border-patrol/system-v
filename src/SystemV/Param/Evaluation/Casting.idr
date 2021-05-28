module SystemV.Param.Evaluation.Casting

import SystemV.Common.Utilities
import SystemV.Param.Types
import SystemV.Param.Terms

import SystemV.Param.Evaluation.Values

%default total

public export
castDir : {dirTo : Direction}
       -> (prf   : ValidDirCast dirFrom dirTo)
                -> Direction
castDir {dirTo} _ = dirTo


public export
cast : {fromPort, toPort : TYPE (IDX TERM)}
    -> (prf   : ValidCast fromPort toPort)
    -> (from  : SystemV ctxt fromPort)
    -> (value : Value from)
             -> SystemV ctxt toPort
cast (CanCast castDir') (MkPort type dirA) (MkPort x dirA)
  = MkPort type
           (castDir castDir')

cast (CanCast castDir) (Seq left right) (Seq x y)
  = Seq left $ cast (CanCast castDir) right y

-- [ EOF ]
