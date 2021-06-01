module SystemV.Core.Evaluation.Progress

import SystemV.Common.Utilities
import SystemV.Core.Types

import SystemV.Core.Terms

import SystemV.Core.Terms.Renaming
import SystemV.Core.Terms.Substitution

import SystemV.Core.Values

import SystemV.Core.Evaluation.Casting
import SystemV.Core.Evaluation.Slicing
import SystemV.Core.Evaluation.Indexing

import SystemV.Core.Evaluation.Reduction

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

progress (TyChan typeD) with (progress typeD)
  progress (TyChan typeD) | (Done value)
    = Done (TyChan value)
  progress (TyChan typeD) | (Step step)
    = Step (SimplifyTyChan step)

progress (TyPort typeD dir) with (progress typeD)
  progress (TyPort typeD dir) | (Done value)
    = Done (TyPort value dir)
  progress (TyPort typeD dir) | (Step step)
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

  progress (App (Seq _ _ IsUnit) _) | (Done (Seq _ _)) impossible
  progress (App (Seq _ _ IsMod) _) | (Done (Seq _ _)) impossible

  progress (App func param) | (Step step)
    = Step (SimplifyFuncAppFunc step)


-- ### Modules, Ports, & Unit

progress MkUnit
  = Done MkUnit


progress EndModule
  = Done EndModule

progress (MkPort typeD dir) with (progress typeD)
  progress (MkPort typeD dir) | (Done value)
    = Done (MkPort value dir)

  progress (MkPort typeD dir) | (Step step)
    = Step (SimplifyMkPort step)

-- ### Channels

progress (MkChan typeD) with (progress typeD)
  progress (MkChan typeD) | (Done value)
    = Done (MkChan value)

  progress (MkChan typeD) | (Step step)
    = Step (SimplifyMkChan step)

progress (WriteTo chan) with (progress chan)
  progress (WriteTo (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceWriteTo

  progress (WriteTo (Seq left right IsUnit)) | (Done (Seq x y)) impossible
  progress (WriteTo (Seq left right IsMod))  | (Done (Seq x y)) impossible
  progress (WriteTo chan) | (Step step)
   = Step (SimplifyWriteTo step)


progress (ReadFrom chan) with (progress chan)
  progress (ReadFrom (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceReadFrom

  progress (ReadFrom (Seq left right IsUnit)) | (Done (Seq x y)) impossible
  progress (ReadFrom (Seq left right IsMod)) | (Done (Seq x y)) impossible


  progress (ReadFrom chan) | (Step step)
   = Step (SimplifyReadFrom step)

progress (Drive chan) with (progress chan)
  progress (Drive (MkPort ty OUT)) | (Done (MkPort tyV OUT))
    = Done (Drive (MkPort tyV OUT))

  progress (Drive (Seq left right IsUnit)) | (Done (Seq x y)) impossible
  progress (Drive (Seq left right IsMod)) | (Done (Seq x y)) impossible

  progress (Drive chan) | (Step step)
   = Step (SimplifyDrive step)

progress (Catch chan) with (progress chan)
  progress (Catch (MkPort ty IN)) | (Done (MkPort tyV IN))
    = Done (Catch (MkPort tyV IN))

  progress (Catch (Seq left right IsUnit)) | (Done (Seq x y)) impossible
  progress (Catch (Seq left right IsMod)) | (Done (Seq x y)) impossible

  progress (Catch chan) | (Step step)
   = Step (SimplifyCatch step)

-- ### Decisions & Connections
progress (IfThenElseR test whenIsZ whenNotZ) with (progress test)
  progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) with (progress whenIsZ)
    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) with (progress whenNotZ)
      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Done false)
        = Done (IfThenElseR (MkPort tyV IN) true false)

      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Step step)
        = Step (SimplifyCondFalse step)

    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Step step)
      = Step (SimplifyCondTrue step)

  progress (IfThenElseR (Seq left right IsMod)  whenIsZ whenNotZ) | (Done (Seq x y)) impossible
  progress (IfThenElseR (Seq left right IsUnit) whenIsZ whenNotZ) | (Done (Seq x y)) impossible

  progress (IfThenElseR test whenIsZ whenNotZ) | (Step step)
    = Step (SimplifyCondTest step)

-- #### Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) with (progress portR)
    progress (Connect (MkPort tyL dirL) (MkPort tyR dirR) prf) | (Done (MkPort x dirL)) | (Done (MkPort y dirR))
      = Done (Connect (MkPort x dirL) (MkPort y dirR))

    progress (Connect (MkPort tyL dirL) (Seq left right IsMod) prf) | (Done (MkPort x dirL)) | (Done (Seq y z)) impossible
    progress (Connect (MkPort tyL dirL) (Seq left right IsUnit) prf) | (Done (MkPort x dirL)) | (Done (Seq y z)) impossible

    progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) | (Step step)
      = Step (SimplifyConnectRight step)

  progress (Connect (Seq left right IsUnit) portR prf) | (Done (Seq x y)) impossible
  progress (Connect (Seq left right IsMod) portR prf) | (Done (Seq x y)) impossible

  progress (Connect portL portR prf) | (Step step)
    = Step (SimplifyConnectLeft step)

-- ### Casting & Slicing
progress (Cast portA prf) with (progress portA)
  progress (Cast (MkPort ty dirA) prf) | (Done (MkPort x dirA))
    = Step (ReduceCast (MkPort x dirA))
  progress (Cast (Seq left right IsMod) prf)  | (Done (Seq x y)) impossible
  progress (Cast (Seq left right IsUnit) prf) | (Done (Seq x y)) impossible


  progress (Cast portA prf) | (Step step)
    = Step (SimplifyCast step)

-- #### Slicing

progress (Slice port alpha omega prf) with (progress port)
  progress (Slice (MkPort tyP dir) alpha omega prf) | (Done (MkPort x dir))
        = Step (ReduceSlice (MkPort x dir))

  progress (Slice (Seq left right IsUnit) alpha omega prf) | (Done (Seq x y)) impossible
  progress (Slice (Seq left right IsMod) alpha omega prf) | (Done (Seq x y)) impossible


  progress (Slice port alpha omega prf) | (Step step)
    = Step (SimplifySlicePort step)

-- #### Indexing
progress (Index n port prf) with (progress port)
  progress (Index n (MkPort ty dir) prf) | (Done (MkPort tyV dir))
    = Step (ReduceIndex (MkPort tyV dir))

  progress (Index n (Seq left right IsUnit) prf) | (Done (Seq x y)) impossible
  progress (Index n (Seq left right IsMod) prf)  | (Done (Seq x y)) impossible

  progress (Index n port prf) | (Step step)
    = Step (SimplifyIndexPort step)



-- ### Gates

-- #### Not
progress (Not portO portI) with (progress portO)
  progress (Not (MkPort ty OUT) portI) | (Done (MkPort tyValO OUT)) with (progress portI)

    progress (Not (MkPort tyO OUT) (MkPort tyI IN)) | (Done (MkPort tyValO OUT)) | (Done (MkPort tyVa IN))
      = Done (Not (MkPort tyValO OUT) (MkPort tyVa IN ))

    progress (Not (MkPort tyO OUT) (Seq left right IsMod)) | (Done (MkPort tyValO OUT)) | (Done (Seq x y)) impossible
    progress (Not (MkPort tyO OUT) (Seq left right IsUnit)) | (Done (MkPort tyValO OUT)) | (Done (Seq x y)) impossible

    progress (Not (MkPort tyO OUT) portI) | (Done (MkPort tyValO OUT)) | (Step step)
      = Step (SimplifyNotIn step)

  progress (Not (Seq left right IsMod) portI) | (Done (Seq x y)) impossible
  progress (Not (Seq left right IsUnit) portI) | (Done (Seq x y)) impossible

  progress (Not portO portI) | (Step step)
    = Step (SimplifyNotOut step)

-- #### Binary

progress (Gate kind portO portIA portIB) with (progress portO)
  progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) with (progress portIA)
    progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) with (progress portIB)
      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (MkPort tyIB IN)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (MkPort tyVIB IN))
        = Done (Gate (MkPort tyV OUT) (MkPort tyVIA IN) (MkPort tyVIB IN))

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (Seq left right IsMod)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (Seq x y)) impossible
      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (Seq left right IsUnit)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (Seq x y)) impossible

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Step step)
        = Step (SimplifyBinInB step)

    progress (Gate kind (MkPort ty OUT) (Seq left right IsUnit) portIB) | (Done (MkPort tyV OUT)) | (Done (Seq x y)) impossible
    progress (Gate kind (MkPort ty OUT) (Seq left right IsMod) portIB) | (Done (MkPort tyV OUT)) | (Done (Seq x y)) impossible

    progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) | (Step step)
      = Step (SimplifyBinInA step)

  progress (Gate kind (Seq left right IsMod) portIA portIB) | (Done (Seq x y)) impossible
  progress (Gate kind (Seq left right IsUnit) portIA portIB) | (Done (Seq x y)) impossible

  progress (Gate kind portO portIA portIB) | (Step step)
    = Step (SimplifyBinOut step)

-- ### Binders
progress (Let value body prf) with (progress value)
  progress (Let value body prf) | (Done val)
    = Step (ReduceLetBody val)

  progress (Let value body prf) | (Step step)
    = Step (SimplifyLetValue step)

-- ### Sequencing
progress (Seq left right prf) {type} with (progress left)

  progress (Seq (Seq l r IsUnit) right prf) {type = type} | (Done (Seq x y))
    = Step RewriteSeq

  progress (Seq left right prf) | (Done value) with (progress right)
    progress (Seq left right prf) | (Done l) | (Done r)
      = Done (Seq l r)

    progress (Seq left right prf) | (Done l) | (Step step)
      = Step (SimplifySeqRight l step)

  progress (Seq left right prf) {type = type} | (Step step)
    = Step (SimplifySeqLeft step)

-- [ EOF ]
