module SystemV.Core.Evaluation

import Data.Fuel

import SystemV.Common.Utilities
import SystemV.Core.Types
import SystemV.Core.Terms


import SystemV.Core.Terms.Renaming

import SystemV.Core.Terms.Substitution

import SystemV.Core.Evaluation.Values
import SystemV.Core.Evaluation.Reduction
import SystemV.Core.Evaluation.Progress

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

public export
covering
run : forall type
    . (this : SystemV Nil type)
           -> Maybe (Subset (SystemV Nil type) (Reduces this))
run this with (compute forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (Element term steps)
  run this | (RunEval steps OOF) = Nothing

public export
data Error = NoFuel

export
Show Evaluation.Error where
  show NoFuel = "NoFuel"

export
covering
eval : forall type
     . (this : SystemV Nil type)
            -> Either Evaluation.Error (SystemV Nil type)
eval this with (run this)
  eval this | Nothing = Left NoFuel
  eval this | (Just (Element fst snd)) = Right fst

-- --------------------------------------------------------------------- [ EOF ]
