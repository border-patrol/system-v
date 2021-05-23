module SystemV.Param.Evaluation

import Data.Fuel

import SystemV.Common.Utilities
import SystemV.Param.Types
import SystemV.Param.Terms


import SystemV.Param.Terms.Renaming

import SystemV.Param.Terms.Substitution

import SystemV.Param.Evaluation.Values
import SystemV.Param.Evaluation.Casting
import SystemV.Param.Evaluation.Sizing
import SystemV.Param.Evaluation.Slicing
import SystemV.Param.Evaluation.Reduction
import public SystemV.Param.Evaluation.Progress

%default total

data Reduces : (this : SystemV ctxt type)
            -> (that : SystemV ctxt type)
            -> Type
  where
    Refl  : {this : SystemV ctxt type}
                 -> Reduces this this
    Trans : {this, that, end : SystemV ctxt type}
         -> Redux this that
         -> Reduces that end
         -> Reduces this end

data Finished : (term : SystemV ctxt type)
                     -> Type
  where
    Normalised : {term : SystemV ctxt type}
                      -> Value term
                      -> Finished term

    ErrorFound : {term   : SystemV ctxt type}
              -> (reason : Progress.Error)
                        -> Finished term

    OOF : Finished term

data Evaluate : (term : SystemV Nil type) -> Type where
  RunEval : {this, that : SystemV Nil type}
         -> (steps      : Inf (Reduces this that))
         -> (result     : Finished that)
                       -> Evaluate this

total
compute : forall type
        . (fuel : Fuel)
       -> (term : SystemV Nil type)
       -> Evaluate term
compute Dry term = RunEval Refl OOF
compute (More fuel) term with (progress term)
  compute (More fuel) term | (Done value) = RunEval Refl (Normalised value)

  compute (More fuel) term | (Step step {that}) with (compute fuel that)
    compute (More fuel) term | (Step step {that = that}) | (RunEval steps result)
      = RunEval (Trans step steps) result
  compute (More fuel) term | (Halt reason) = RunEval Refl (ErrorFound reason)

namespace Param
  public export
  data Error = NoFuel | RunTime Progress.Error

  export
  Show Progress.Error where
    show  VectorCannotBeZero     = "Err"
    show  (IndexOutOfBounds n w) = "Err"
    show  (InvalidCast err)      = "Err"
    show  (InvalidBound err)     = "Err"
    show  (UnexpectedSeq)        = "Err"
    show  (ArithOpError err)     = "Err"

  export
  Show Param.Error where
    show NoFuel = "NoFuel"
    show (RunTime err) = show err



  covering
  run : forall type
      . (this : SystemV Nil type)
             -> Either Param.Error
                       (DPair (SystemV Nil type) (Reduces this))
  run this with (compute forever this)
    run this | (RunEval steps (Normalised {term} x))
      = Right (term ** steps)

    run this | (RunEval steps (ErrorFound err))
      = Left (RunTime err)

    run this | (RunEval steps OOF) = Left NoFuel


  export
  covering
  eval : forall type
       . (this : SystemV Nil type)
              -> Either Param.Error (SystemV Nil type)
  eval this with (run this)
    eval this | Left err = Left err
    eval this | Right (fst ** snd) = Right fst

-- --------------------------------------------------------------------- [ EOF ]
