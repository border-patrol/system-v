module SystemV.Params.Evaluation.Casting

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Equality

%default total

public export
castDir : {dirTo : Direction}
       -> (prf   : ValidDirCast dirFrom dirTo)
                -> Direction
castDir {dirTo} _ = dirTo

public export
data Error = TypeMismatch (SystemV Nil DATATERM) (SystemV Nil DATATERM)

public export
data CheckCast : (prf   : ValidCast fromPort toPort)
              -> (from  : SystemV Nil fromPort)
              -> (value : Value from)
              -> (to    : SystemV Nil DATATERM)
              -> (vd    : Value to)
                       -> Type
  where
    CC : {prf : ValidCast (PortTy from) (PortTy to)}
      -> (DataEq tyA tyB)
      -> CheckCast prf (MkPort fcA tyA from) (MkPort tyAV from)
                       tyB                   tyBV


export
checkCast : (prf   : ValidCast fromPort toPort)
         -> (from  : SystemV Nil fromPort)
         -> (value : Value from)
         -> (to    : SystemV Nil DATATERM)
         -> (vd    : Value to)
                  -> Either Casting.Error (CheckCast prf from value to vd)
checkCast (CanCast castDir) from value to vt with (value)
  checkCast (CanCast castDir) (MkPort fcA type dirA) value to vt | (MkPort x dirA) with (Data.decEq type x to vt)
    checkCast (CanCast castDir) (MkPort fcA type dirA) value to vt | (MkPort x dirA) | (Yes prf)
      = Right (CC prf)
    checkCast (CanCast castDir) (MkPort fcA type dirA) value to vt | (MkPort x dirA) | (No contra)
      = Left (TypeMismatch type to)
  checkCast (CanCast _) (Seq _ _ _ IsUnit) _ _ _ | (Seq _ _) impossible
  checkCast (CanCast _) (Seq _ _ _ IsMod)  _ _ _ | (Seq _ _) impossible

public export
cast : {fromPort, toPort : TYPE (IDX TERM)}
    -> (prf   : ValidCast fromPort toPort)
    -> (from  : SystemV Nil fromPort)
    -> (value : Value from)
    -> (to    : SystemV Nil DATATERM)
    -> (vd    : Value to)
    ->          CheckCast prf from value to vd
             -> SystemV Nil toPort
cast (CanCast castDir') (MkPort fcA tyA from) (MkPort tyAV from) tyB vd (CC prf)
  = MkPort fcA tyB (castDir castDir')

-- [ EOF ]
