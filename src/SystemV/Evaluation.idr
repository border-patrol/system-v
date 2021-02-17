module SystemV.Evaluation

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms
import SystemV.Values

import SystemV.Terms.Renaming
import SystemV.Terms.Substitution
import SystemV.Terms.Reduction

import SystemV.Evaluation.Progress

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
data Fuel = Empty | More (Lazy Fuel)

public export
covering
forever : Fuel
forever = More forever

public export
total
compute : forall type
        . (fuel : Fuel)
       -> (term : SystemV Nil type)
       -> Evaluate term
compute Empty term = RunEval Refl OOF
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
