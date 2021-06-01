module SystemV.Annotated.Evaluation.Casting

import SystemV.Common.Utilities
import SystemV.Annotated.Types
import SystemV.Annotated.Terms

import SystemV.Annotated.Values

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
castSense : {senseTo : Sensitivity}
         -> (prf     : Compatible senseFrom senseTo)
                    -> Sensitivity
castSense {senseTo} _ = senseTo

public export
castIntent : {to  : Intention}
          -> (prf : Compatible from to)
                 -> Intention
castIntent {to} _ = to

public export
cast : {fromPort, toPort : TYPE (IDX TERM)}
    -> (prf   : ValidCast fromPort toPort)
    -> (from  : SystemV ctxt fromPort)
    -> (value : Value from)
             -> SystemV ctxt toPort
cast (CanCast castTy' castDir' castSense' castIntent') (MkPort type dirA sA iA) (MkPort x)
  = MkPort (castTy castTy' type x)
           (castDir castDir')
           (castSense castSense')
           (castIntent castIntent')

cast (CanCast _ _ _ _) (Seq _ _ IsUnit) (Seq _ _) impossible
cast (CanCast _ _ _ _) (Seq _ _ IsMod) (Seq _ _) impossible

-- [ EOF ]
