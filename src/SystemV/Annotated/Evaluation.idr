module SystemV.Annotated.Evaluation

import Data.Fuel

import SystemV.Common.Utilities
import SystemV.Annotated.Types
import SystemV.Annotated.Terms

import SystemV.Annotated.Terms.Renaming
import SystemV.Annotated.Terms.Substitution

import SystemV.Annotated.Values

import SystemV.Annotated.Evaluation.Reduction
import SystemV.Annotated.Evaluation.Progress

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

covering
run : forall type
    . (this : SystemV Nil type)
           -> Maybe (Subset (SystemV Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

namespace Annotated
  public export
  data Error = NoFuel

  export
  Show Evaluation.Annotated.Error where
    show NoFuel = "NoFuel"

  export
  covering
  eval : forall type
       . (this : SystemV Nil type)
              -> Either Evaluation.Annotated.Error (SystemV Nil type)
  eval this with (run this)
    eval this | Nothing = Left NoFuel
    eval this | (Just (Element fst snd)) = Right fst

-- --------------------------------------------------------------------- [ EOF ]
