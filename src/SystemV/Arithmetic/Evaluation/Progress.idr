module SystemV.Arithmetic.Evaluation.Progress

import SystemV.Utilities
import SystemV.Types

import SystemV.Arithmetic.Terms
import SystemV.Arithmetic.Values
import SystemV.Arithmetic.Terms.Renaming
import SystemV.Arithmetic.Terms.Substitution
import SystemV.Arithmetic.Terms.Casting
import SystemV.Arithmetic.Terms.Reduction

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

progress (TyVect size type) with (progress type)
  progress (TyVect size type) | (Done typeValue) = Done (TyVect size typeValue)
  progress (TyVect size type) | (Step step) = Step (SimplifyTyVect step)

progress TyBool = Done TyBool
progress (B b)  = Done B

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

progress (Drive chan) with (progress chan)
  progress (Drive chan) | Done chanVal
      = Done (Drive chanVal)

  progress (Drive chan) | Step step
    = Step (SimplifyDrive step)

progress (Catch chan) with (progress chan)
  progress (Catch chan) | Done value
    = Done (Catch value)
  progress (Catch chan) | Step step
    = Step (SimplifyCatch step)

-- Runtime wiring decisions
progress (IfThenElseR cond true false) with (progress cond)
  progress (IfThenElseR cond true false) | Done condVal with (progress true)
    progress (IfThenElseR cond true false) | Done condVal | Done trueVal with (progress false)
      progress (IfThenElseR cond true false) | Done condVal | Done trueVal | Done falseVal
        = Done (IfThenElseR condVal trueVal falseVal)

      progress (IfThenElseR cond true false) | Done condVal | Done trueVal | Step step
        = Step (SimplifyIfThenElseRFalse condVal trueVal step)

    progress (IfThenElseR cond true false) | Done condVal | Step step
      = Step (SimplifyIfThenElseRTrue condVal step)

  progress (IfThenElseR cond true false) | Step step
    = Step (SimplifyIfThenElseRCond step)

-- Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect portL portR prf) | Done portLV with (progress portR)
    progress (Connect portL portR prf) | Done portLV | Done portRV
      = Done (Connect portLV portRV)

    progress (Connect portL portR prf) | Done portLV | Step step
      = Step (SimplifyConnectRight portLV step)

  progress (Connect portL portR prf) | Step step
    = Step (SimplifyConnectLeft step)

progress (Cast this prf) with (progress this)
  progress (Cast (MkPort thisPort thisDir) prf) | Done (MkPort thisPortV thisDir)
        = Step (ReduceCast (MkPort thisPortV thisDir) prf)
  progress (Cast this prf) | Step step
    = Step (SimplifyCast step)

progress (Slice this a o prf) with (progress this)
  progress (Slice (MkPort type' dir) a o prf) | (Done (MkPort x dir)) with (prf)
    progress (Slice (MkPort (TyVect s etype) dir) a o prf) | (Done (MkPort (TyVect s etypeV) dir)) | (YesCanSlice ArraysAre prfB)
      = Step (ReduceSlice (MkPort (TyVect (sizeFromBound a o prfB) etypeV) dir) (YesCanSlice ArraysAre prfB))

  progress (Slice this a o prf) | (Step step)
    = Step (SimplifySlice step)

-- Params
progress TyParam = Done TyParam
progress (MkParam val) = Done MkParam

progress (ParamOpBool op l r) with (progress l)
  progress (ParamOpBool op l r) | Done lval with (progress r)
    progress (ParamOpBool op (MkParam l) (MkParam r)) | Done MkParam | Done MkParam
      = Step ReduceParamOpBool

    progress (ParamOpBool op l r) | Done lval | Step step
      = Step (SimplifyParamOpBoolRight lval step)

  progress (ParamOpBool op l r) | Step step
    = Step (SimplifyParamOpBoolLeft step)

progress (ParamOpArith op l r) with (progress l)
  progress (ParamOpArith op l r) | Done lval with (progress r)
    progress (ParamOpArith op (MkParam l) (MkParam r)) | Done MkParam | Done MkParam
      = Step ReduceParamOpArith

    progress (ParamOpArith op l r) | Done lval | Step step
      = Step (SimplifyParamOpArithRight lval step)

  progress (ParamOpArith op l r) | Step step
    = Step (SimplifyParamOpArithLeft step)

progress (ParamOpNot p) with (progress p)
  progress (ParamOpNot (B b)) | Done B
    = Step ReduceParamOpNot
  progress (ParamOpNot p) | Step step
    = Step (SimplifyParamOpNot step)

progress (IfThenElseC cond t f) with (progress cond)
  progress (IfThenElseC (B True) true false) | Done B
    = Step ReduceIfThenElseCTrue
  progress (IfThenElseC (B False) true false) | Done B
    = Step ReduceIfThenElseCFalse

  progress (IfThenElseC cond true false) | Step step
    = Step (SimplifyIfThenElseCCond step)

-- Gates
progress (Not out input) with (progress out)
  progress (Not out input) | (Done outV) with (progress input)
    progress (Not out input) | (Done outV) | Done inputV
      = Done (Not outV inputV)
    progress (Not out input) | (Done outV) | Step step
      = Step (SimplifyNotInput outV step)

  progress (Not out input) | (Step step)
    = Step (SimplifyNotOutput step)

progress (Gate type out ia ib) with (progress out)
  progress (Gate type out ia ib) | Done outV with (progress ia)
    progress (Gate type out ia ib) | Done outV | Done iaV with (progress ib)
      progress (Gate type out ia ib) | Done outV | Done iaV | Done ibV
        = Done (Gate outV iaV ibV)

      progress (Gate type out ia ib) | Done outV | Done iaV | Step step
        = Step (SimplifyGateInputB outV iaV step)

    progress (Gate type out ia ib) | Done outV | Step step
      = Step (SimplifyGateInputA outV step)

  progress (Gate type out ia ib) | Step step
    = Step (SimplifyGateOutput step)


-- Binders
progress (Let value body) with (progress value)
  progress (Let value body) | Done this
    = Step (ReduceLetBody this)

  progress (Let value body) | Step step
    = Step (SimplifyLetValue step)

-- --------------------------------------------------------------------- [ EOF ]
