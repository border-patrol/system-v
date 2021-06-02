module SystemV.Params.Evaluation

import Data.Fuel

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms


import SystemV.Params.Terms.Renaming

import SystemV.Params.Terms.Substitution

import public SystemV.Params.Evaluation.Error
import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Casting

import SystemV.Params.Evaluation.Slicing
import SystemV.Params.Evaluation.Reduction
import SystemV.Params.Evaluation.Progress

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
              -> (reason : Params.Evaluation.Error)
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

namespace Params

  covering
  run : forall type
      . (this : SystemV Nil type)
             -> Either Params.Evaluation.Error
                       (DPair (SystemV Nil type) (Reduces this))
  run this with (compute forever this)
    run this | (RunEval steps (Normalised {term} x))
      = Right (term ** steps)

    run this | (RunEval steps (ErrorFound err))
      = Left err

    run this | (RunEval steps OOF) = Left NoFuel


  export
  covering
  eval : forall type
       . (this : SystemV Nil type)
              -> Either Params.Evaluation.Error (SystemV Nil type)
  eval this with (run this)
    eval this | Left err = Left err
    eval this | Right (fst ** snd) = Right fst

-- --------------------------------------------------------------------- [ EOF ]
