module SystemV.Evaluation.Progress

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms
import SystemV.Values

import SystemV.Terms.Renaming
import SystemV.Terms.Substitution
import SystemV.Terms.Reduction

%default total

public export
data Progress : (term : SystemV Nil type)
                     -> Type
  where
    Done : forall mty . {term : SystemV Nil mty}
                      -> Value term
                      -> Progress term
    Step : {this, that : SystemV Nil type}
        -> (prf        : Redux this that)
                      -> Progress this

public export
covering
progress : (term : SystemV Nil type)
        -> Progress term
-- STLC
progress {type} (Var _) impossible
progress (Func body) = Done Func
progress (App func var) with (progress func)
  progress (App func var) | (Done prfF) with (progress var)
    progress (App (Func b) var) | (Done prfF) | (Done prfV)
      = Step (ReduceFunc prfV {body=b})
    progress (App func var) | (Done prfF) | (Step prfV)
      = Step (SimplifyFuncAppVar prfF prfV)
  progress (App func var) | (Step prfF)
    = Step (SimplifyFuncAppFunc prfF)

progress (TyFunc param return) with (progress param)
  progress (TyFunc param return) | (Done valueP) with (progress return)
    progress (TyFunc param return) | (Done valueP) | (Done valueR)
      = Done (TyFunc valueP valueR)
    progress (TyFunc param return) | (Done valueP) | (Step prfR)
      = Step (SimplifyTyFuncBody valueP prfR)
  progress (TyFunc param return) | (Step prfP)
    = Step (SimplifyTyFuncParam prfP)

-- Unit
progress TyUnit = Done TyUnit
progress MkUnit = Done MkUnit

-- Type Constructors
progress TyLogic = Done TyLogic
progress L       = Done Logic

-- Modules
progress TyModule  = Done TyModule
progress EndModule = Done EndModule

-- TypeDef Type & Value Constructors, and Matching.
progress (TypeDefType type) with (progress type)
  progress (TypeDefType type) | (Done valueT) = Done (TypeDefType valueT)
  progress (TypeDefType type) | (Step prfT) = Step (SimplifyTypeDefType prfT)

progress (TypeDefCTor type value prf) with (progress type)
  progress (TypeDefCTor type value prf) | (Done valueT) with (progress value)
    progress (TypeDefCTor type value prf) | (Done valueT) | (Done valueV)
      = Done (TypeDefCTor valueV)
    progress (TypeDefCTor type value prf) | (Done valueT) | (Step prfV)
      = Step (SimplifyTypeDefCTorValue valueT prfV)
  progress (TypeDefCTor type value prf) | (Step prfT)
      = Step (SimplifyTypeDefCTorType prfT)

progress (TypeDef desc body) with (progress desc)
  progress (TypeDef desc body) | (Done valueD)
    = Step (ReduceTypeDef valueD)
  progress (TypeDef desc body) | (Step prfD)
   = Step (SimplifyTypeDef prfD)

-- Ports
progress (TyPort type dir) with (progress type)
  progress (TyPort type dir) | Done (valueTy)
    = Done (TyPort valueTy dir)
  progress (TyPort type dir) | (Step step)
    = Step (SimplifyTyPort step)

progress (MkPort type dir) with (progress type)
  progress (MkPort type dir) | Done (valueTy)
    = Done (MkPort valueTy dir)
  progress (MkPort type dir) | (Step step)
    = Step (SimplifyMkPort step)

-- Channels
progress (TyChan type) with (progress type)
  progress (TyChan type) | Done (valueTy)
    = Done (TyChan valueTy)
  progress (TyChan type) | (Step step)
    = Step (SimplifyTyChan step)

progress (MkChan type) with (progress type)
  progress (MkChan type) | Done (valueTy)
    = Done (MkChan valueTy)
  progress (MkChan type) | (Step step)
    = Step (SimplifyMkChan step)

progress (WriteTo chan) with (progress chan)
  progress (WriteTo (MkChan typeD)) | Done (MkChan typeV)
    = Step (ReduceWriteTo typeV)
  progress (WriteTo chan) | Step step
    = Step (SimplifyWriteTo step)

progress (ReadFrom chan) with (progress chan)
  progress (ReadFrom (MkChan typeD)) | Done (MkChan typeV)
    = Step (ReduceReadFrom typeV)
  progress (ReadFrom chan) | Step step
    = Step (SimplifyReadFrom step)


-- Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect portL portR prf) | Done portLV with (progress portR)
    progress (Connect portL portR prf) | Done portLV | Done portRV
      = Done (Connect portLV portRV)

    progress (Connect portL portR prf) | Done portLV | Step step
      = Step (SimplifyConnectRight portLV step)

  progress (Connect portL portR prf) | Step step
    = Step (SimplifyConnectLeft step)

-- Params
progress (TyParam type) with (progress type)
  progress (TyParam type) | Done (valueTy)
    = Done (TyParam valueTy)
  progress (TyParam type) | (Step step)
    = Step (SimplifyTyParam step)

progress (MkParam type) with (progress type)
  progress (MkParam type) | Done (valueTy)
    = Done (MkParam valueTy)
  progress (MkParam type) | (Step step)
    = Step (SimplifyMkParam step)

-- Binders
progress (Let type value prf body) with (progress type)
  progress (Let type value prf body) | (Done valueT) with (progress value)
    progress (Let type value prf body) | (Done valueT) | (Done valueV)
      = Step (ReduceLetBody valueT valueV)
    progress (Let type value prf body) | (Done valueT) | (Step prfV)
      = Step (SimplifyLetValue valueT prfV)
  progress (Let type value prf body) | (Step stepT)
    = Step (SimplifyLetType stepT)

-- --------------------------------------------------------------------- [ EOF ]
