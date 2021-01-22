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
progress : (term : SystemV Nil type)
        -> Progress term
-- STLC
progress {type} (Var _) impossible
progress (Func theType body prf) = Done Func

progress (App func var) with (progress func)
  progress (App func var) | (Done prfF) with (progress var)
    progress (App (Func theType b prfTyCheck) var) | (Done prfF) | (Done prfV)
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
progress I       = Done I
progress O       = Done O
progress X       = Done X
progress Z       = Done Z

progress (TyVect size type) with (progress type)
  progress (TyVect size type) | (Done typeValue) = Done (TyVect typeValue)
  progress (TyVect size type) | (Step step) = Step (SimplifyTyVect step)
progress V = Done Vect

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

progress (Drive chan val prf) with (progress chan)
  progress (Drive chan val prf) | Done chanVal with (progress val)
    progress (Drive chan val prf) | Done chanVal | Done valueVal
      = Done (Drive chanVal valueVal)

    progress (Drive chan val prf) | Done chanVal | Step step
      = Step (SimplifyDriveVal chanVal step)

  progress (Drive chan val prf) | Step step
    = Step (SimplifyDriveChan step)

progress (Catch chan) with (progress chan)
  progress (Catch chan) | Done value
    = Done (Catch value)
  progress (Catch chan) | Step step
    = Step (SimplifyCatch step)

-- Booleans
progress (IsOnParam param) with (progress param)
  progress (IsOnParam param) | Done val
    = Done (IsOnParam val)
  progress (IsOnParam param) | Step step
    = Step (SimplifyIsOnParam step)

progress (IsOnPort port) with (progress port)
  progress (IsOnPort port) | Done val
    = Done (IsOnPort val)
  progress (IsOnPort port) | Step step
    = Step (SimplifyIsOnPort step)

progress (IfThenElse cond true false) with (progress cond)
  progress (IfThenElse cond true false) | Done condVal with (progress true)
    progress (IfThenElse cond true false) | Done condVal | Done trueVal with (progress false)
      progress (IfThenElse cond true false) | Done condVal | Done trueVal | Done falseVal
        = Done (IfThenElse condVal trueVal falseVal)

      progress (IfThenElse cond true false) | Done condVal | Done trueVal | Step step
        = Step (SimplifyIfThenElseFalse condVal trueVal step)

    progress (IfThenElse cond true false) | Done condVal | Step step
      = Step (SimplifyIfThenElseTrue condVal step)

  progress (IfThenElse cond true false) | Step step
    = Step (SimplifyIfThenElseCond step)

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
progress (Let value body) with (progress value)
  progress (Let value body) | Done this
    = Step (ReduceLetBody this)

  progress (Let value body) | Step step
    = Step (SimplifyLetValue step)

-- --------------------------------------------------------------------- [ EOF ]
