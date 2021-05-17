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
cast (CanCast castTy' castDir' castSense' castIntent') from value with (value)
  cast (CanCast castTy' castDir' castSense' castIntent') (MkPort type dirA sA iA) value | (MkPort v)
    = MkPort (castTy castTy' type v)
             (castDir castDir')
             (castSense castSense')
             (castIntent castIntent')

  cast (CanCast castTy' castDir' castSense' castIntent') (Seq left right) value | (Seq x y)
    = Seq left $ cast (CanCast castTy' castDir' castSense' castIntent') right y

-- [ EOF ]
