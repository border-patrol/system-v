module SystemV.Param.Evaluation.Casting

import SystemV.Common.Utilities
import SystemV.Param.Types
import SystemV.Param.Terms

import SystemV.Param.Evaluation.Values
import SystemV.Param.Evaluation.Equality

%default total

public export
castDir : {dirTo : Direction}
       -> (prf   : ValidDirCast dirFrom dirTo)
                -> Direction
castDir {dirTo} _ = dirTo

public export
data Error = UnexpectedSeq
           | TypeMismatch (SystemV Nil DATATERM) (SystemV Nil DATATERM)

public export
data CheckCast : (prf   : ValidCast fromPort toPort)
              -> (from  : SystemV Nil fromPort)
              -> (value : Value from)
              -> (to    : SystemV Nil DATATERM)
              -> (vd    : Value to)
                       -> Type
  where
    CC : {prf : ValidCast (PortTy from) (PortTy to)}
      -> (tyA === tyB)
      -> CheckCast prf (MkPort tyA from) (MkPort tyAV from)
                       tyB               tyBV


export
checkCast : (prf   : ValidCast fromPort toPort)
         -> (from  : SystemV Nil fromPort)
         -> (value : Value from)
         -> (to    : SystemV Nil DATATERM)
         -> (vd    : Value to)
                  -> Either Casting.Error (CheckCast prf from value to vd)
checkCast (CanCast castDir) from value to vt with (value)
  checkCast (CanCast castDir) (MkPort type dirA) value to vt | (MkPort x dirA) with (Data.decEq type x to vt)
    checkCast (CanCast castDir) (MkPort type dirA) value to vt | (MkPort x dirA) | (Yes prf)
      = Right (CC prf)
    checkCast (CanCast castDir) (MkPort type dirA) value to vt | (MkPort x dirA) | (No contra)
      = Left (TypeMismatch type to)
  checkCast (CanCast castDir) (Seq left right) value to vt| (Seq x y)
    = Left UnexpectedSeq

public export
cast : {fromPort, toPort : TYPE (IDX TERM)}
    -> (prf   : ValidCast fromPort toPort)
    -> (from  : SystemV Nil fromPort)
    -> (value : Value from)
    -> (to    : SystemV Nil DATATERM)
    -> (vd    : Value to)
    ->          CheckCast prf from value to vd
             -> SystemV Nil toPort
cast (CanCast castDir') (MkPort tyA from) (MkPort tyAV from) tyA vd (CC Refl)
  = MkPort tyA (castDir castDir')

-- [ EOF ]
