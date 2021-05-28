module SystemV.Annotated.Evaluation.Progress

import SystemV.Common.Utilities
import SystemV.Annotated.Types

import SystemV.Annotated.Terms

import SystemV.Annotated.Terms.Renaming
import SystemV.Annotated.Terms.Substitution

import SystemV.Annotated.Values

import SystemV.Annotated.Evaluation.Casting
import SystemV.Annotated.Evaluation.Slicing
import SystemV.Annotated.Evaluation.Indexing

import SystemV.Annotated.Evaluation.Reduction

%default total

public export
data Progress : (term : SystemV Nil type)
                     -> Type
  where
    Done : forall mty . {term  : SystemV Nil mty}
                     -> (value : Value term)
                              -> Progress term

    Step : {this, that : SystemV Nil type}
        -> (step       : Redux this that)
                      -> Progress this

public export
progress : (term : SystemV Nil type)
        -> Progress term

-- [ Types ]
progress TyUnit
  = Done TyUnit

progress TyModule
  = Done TyModule

progress (TyChan typeD sense intent) with (progress typeD)
  progress (TyChan typeD sense intent) | (Done value)
    = Done (TyChan value)
  progress (TyChan typeD sense intent) | (Step step)
    = Step (SimplifyTyChan step)

progress (TyPort typeD dir sense intent) with (progress typeD)
  progress (TyPort typeD dir sense intent) | (Done value)
    = Done (TyPort value)
  progress (TyPort typeD dir sense intent) | (Step step)
    = Step (SimplifyTyPort step)

progress TyLogic
  = Done TyLogic

progress (TyVect s typeE) with (progress typeE)
  progress (TyVect s typeE) | (Done value)
    = Done (TyVect s value)

  progress (TyVect s typeE) | (Step step)
    = Step (SimplifyTyVect step)

-- [ Terms ]

-- ### STLC
progress (Var _) impossible

progress (Func x body prf vld) = Done Func

progress (App func param) with (progress func)
  progress (App (Func ty body prf vld) param) | (Done Func) with (progress param)

    progress (App (Func ty body prf vld) param) | (Done Func) | (Done value)
      = Step (ReduceFunc value {body=body})

    progress (App (Func ty body prf vld) param) | (Done Func) | (Step step)
      = Step (SimplifyFuncAppVar Func step)

  progress (App (Seq left right) param) | (Done (Seq x y))
    = Step RewriteFuncAppFunc

  progress (App func param) | (Step step)
    = Step (SimplifyFuncAppFunc step)

-- ### Modules, Ports, & Unit

progress MkUnit
  = Done MkUnit


progress EndModule
  = Done EndModule

progress (MkPort typeD dir sense intent) with (progress typeD)
  progress (MkPort typeD dir sense intent) | (Done value)
    = Done (MkPort value)

  progress (MkPort typeD dir sense intent) | (Step step)
    = Step (SimplifyMkPort step)

-- ### Channels

progress (MkChan typeD sense intent) with (progress typeD)
  progress (MkChan typeD sense intent) | (Done value)
    = Done (MkChan value)

  progress (MkChan typeD sense intent) | (Step step)
    = Step (SimplifyMkChan step)

progress (WriteTo chan) with (progress chan)
  progress (WriteTo (MkChan port sense intent)) | (Done (MkChan portVal))
    = Step ReduceWriteTo
  progress (WriteTo (Seq left right)) | (Done (Seq x y))
    = Step RewriteWriteTo
  progress (WriteTo chan) | (Step step)
   = Step (SimplifyWriteTo step)

progress (ReadFrom chan) with (progress chan)
  progress (ReadFrom (MkChan port sense intent)) | (Done (MkChan portVal))
    = Step ReduceReadFrom
  progress (ReadFrom (Seq left right)) | (Done (Seq x y))
    = Step RewriteReadFrom
  progress (ReadFrom chan) | (Step step)
   = Step (SimplifyReadFrom step)

progress (Drive sense intent chan) with (progress chan)
  progress (Drive sense intent (MkPort ty OUT sense intent)) | (Done (MkPort tyV))
    = Done (Drive (MkPort tyV))
  progress (Drive sense intent  (Seq left right)) | (Done (Seq x y))
    = Step RewriteDrive
  progress (Drive sense intent chan) | (Step step)
   = Step (SimplifyDrive step)

progress (Catch chan) with (progress chan)
  progress (Catch (MkPort ty IN sense intent)) | (Done (MkPort tyV))
    = Done (Catch (MkPort tyV))
  progress (Catch (Seq left right)) | (Done (Seq x y))
    = Step RewriteCatch

  progress (Catch chan) | (Step step)
   = Step (SimplifyCatch step)

-- ### Decisions & Connections
progress (IfThenElseR test whenIsZ whenNotZ) with (progress test)
  progress (IfThenElseR (MkPort ty IN sense intent) whenIsZ whenNotZ) | (Done (MkPort tyV)) with (progress whenIsZ)
    progress (IfThenElseR (MkPort ty IN sense intent) whenIsZ whenNotZ) | (Done (MkPort tyV)) | (Done true) with (progress whenNotZ)
      progress (IfThenElseR (MkPort ty IN sense intent) whenIsZ whenNotZ) | (Done (MkPort tyV)) | (Done true) | (Done false)
        = Done (IfThenElseR (MkPort tyV) true false)

      progress (IfThenElseR (MkPort ty IN sense intent) whenIsZ whenNotZ) | (Done (MkPort tyV)) | (Done true) | (Step step)
        = Step (SimplifyCondFalse step)

    progress (IfThenElseR (MkPort ty IN sense intent) whenIsZ whenNotZ) | (Done (MkPort tyV)) | (Step step)
      = Step (SimplifyCondTrue step)

  progress (IfThenElseR (Seq left right) whenIsZ whenNotZ) | (Done (Seq x y))
    = Step RewriteCondTest

  progress (IfThenElseR test whenIsZ whenNotZ) | (Step step)
    = Step (SimplifyCondTest step)

-- #### Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect (MkPort tyL dirL sense intent) portR prf) | (Done (MkPort x)) with (progress portR)
    progress (Connect (MkPort tyL dirL sense intent) (MkPort tyR dirR sense intent) prf) | (Done (MkPort x)) | (Done (MkPort y))
      = Done (Connect (MkPort x) (MkPort y))

    progress (Connect (MkPort tyL dirL sense intent) (Seq left right) prf) | (Done (MkPort x)) | (Done (Seq y z))
      = Step RewriteConnectRight

    progress (Connect (MkPort tyL dirL sense intent) portR prf) | (Done (MkPort x)) | (Step step)
      = Step (SimplifyConnectRight step)

  progress (Connect (Seq left right) portR prf) | (Done (Seq x y))
    = Step RewriteConnectLeft

  progress (Connect portL portR prf) | (Step step)
    = Step (SimplifyConnectLeft step)

-- ### Casting & Slicing
progress (Cast portA prf) with (progress portA)
  progress (Cast (MkPort ty dirA sense intent) prf) | (Done (MkPort x))
    = Step (ReduceCast (MkPort x))
  progress (Cast (Seq left right) prf) | (Done (Seq x y))
    = Step RewriteCast

  progress (Cast portA prf) | (Step step)
    = Step (SimplifyCast step)

-- #### Slicing

progress (Slice port alpha omega prf) with (progress port)
  progress (Slice (MkPort tyP dir sense intent) alpha omega prf) | (Done (MkPort x))
        = Step (ReduceSlice (MkPort x))

  progress (Slice (Seq left right) alpha omega prf) | (Done (Seq x y))
    = Step RewriteSlicePort

  progress (Slice port alpha omega prf) | (Step step)
    = Step (SimplifySlicePort step)

-- #### Indexing
progress (Index n port prf) with (progress port)
  progress (Index n (MkPort ty dir sense intent) prf) | (Done (MkPort tyV))
    = Step (ReduceIndex (MkPort tyV))

  progress (Index n (Seq left right) prf) | (Done (Seq x y))
    = Step RewriteIndexPort

  progress (Index n port prf) | (Step step)
    = Step (SimplifyIndexPort step)

-- ### Gates

-- #### Not
progress (Not portO portI) with (progress portO)
  progress (Not (MkPort tyO OUT sense intent) portI) | (Done (MkPort tyValO)) with (progress portI)

    progress (Not (MkPort tyO OUT sense intent) (MkPort tyI IN sense intent)) | (Done (MkPort tyValO)) | (Done (MkPort tyVa))
      = Done (Not (MkPort tyValO) (MkPort tyVa))

    progress (Not (MkPort tyO OUT sense intent) (Seq left right)) | (Done (MkPort tyValO)) | (Done (Seq x y))
      = Step RewriteNotInSeq

    progress (Not (MkPort tyO OUT sense intent) portI) | (Done (MkPort tyValO)) | (Step step)
      = Step (SimplifyNotIn step)

  progress (Not (Seq left right) portI) | (Done (Seq x y))
    = Step RewriteNotOutSeq

  progress (Not portO portI) | (Step step)
    = Step (SimplifyNotOut step)

-- #### Binary

progress (Gate kind portO portIA portIB) with (progress portO)
  progress (Gate kind (MkPort ty OUT sense intent) portIA portIB) | (Done (MkPort tyV)) with (progress portIA)
    progress (Gate kind (MkPort ty OUT sense intent) (MkPort tyIA IN sense intent) portIB) | (Done (MkPort tyV)) | (Done (MkPort tyVIA)) with (progress portIB)
      progress (Gate kind (MkPort ty OUT sense intent) (MkPort tyIA IN sense intent) (MkPort tyIB IN sense intent)) | (Done (MkPort tyV)) | (Done (MkPort tyVIA)) | (Done (MkPort tyVIB))
        = Done (Gate (MkPort tyV) (MkPort tyVIA) (MkPort tyVIB))

      progress (Gate kind (MkPort ty OUT sense intent) (MkPort tyIA IN sense intent) (Seq left right)) | (Done (MkPort tyV)) | (Done (MkPort tyVIA)) | (Done (Seq x y))
        = Step RewriteBinInB

      progress (Gate kind (MkPort ty OUT sense intent) (MkPort tyIA IN sense intent) portIB) | (Done (MkPort tyV)) | (Done (MkPort tyVIA)) | (Step step)
        = Step (SimplifyBinInB step)

    progress (Gate kind (MkPort ty OUT sense intent) (Seq left right) portIB) | (Done (MkPort tyV)) | (Done (Seq x y))
      = Step RewriteBinInA

    progress (Gate kind (MkPort ty OUT sense intent) portIA portIB) | (Done (MkPort tyV)) | (Step step)
      = Step (SimplifyBinInA step)

  progress (Gate kind (Seq left right) portIA portIB) | (Done (Seq x y))
    = Step RewriteBinOut

  progress (Gate kind portO portIA portIB) | (Step step)
    = Step (SimplifyBinOut step)

-- ### Binders
progress (Let value body) with (progress value)
  progress (Let value body) | (Done val)
    = Step (ReduceLetBody val)

  progress (Let value body) | (Step step)
    = Step (SimplifyLetValue step)

-- ### Sequencing
progress (Seq left right) with (progress left)

  progress (Seq (Seq x y) right) | (Done (Seq xVal yVal))
    = Step RewriteSeq

  progress (Seq left right) | (Done leftVal) with (progress right)
    progress (Seq left right) | (Done leftVal) | (Done rightVal)
      = Done (Seq leftVal rightVal)

    progress (Seq left right) | (Done leftVal) | (Step step)
      = Step (SimplifySeqRight leftVal step)

  progress (Seq left right) | (Step step)
    = Step (SimplifySeqLeft step)

-- [ EOF ]
