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
import SystemV.Param.Evaluation.Progress

%default total

public export
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

public export
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

public export
data Evaluate : (term : SystemV Nil type) -> Type where
  RunEval : {this, that : SystemV Nil type}
         -> (steps      : Inf (Reduces this that))
         -> (result     : Finished that)
                       -> Evaluate this

public export
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

public export
data Error = NoFuel | RunTime Progress.Error

public export
covering
run : forall type
    . (this : SystemV Nil type)
           -> Either Evaluation.Error
                     (Subset (SystemV Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Right (Element term steps)

  run this | (RunEval steps (ErrorFound err))
    = Left (RunTime err)

  run this | (RunEval steps OOF) = Left NoFuel


export
covering
eval : forall type
     . (this : SystemV Nil type)
            -> Either Evaluation.Error (SystemV Nil type)
eval this with (run this)
  eval this | Left err = Left err
  eval this | Right (Element fst snd) = Right fst

-- --------------------------------------------------------------------- [ EOF ]
