module SystemV.Evaluation.Progress

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms


import SystemV.Terms.Renaming
import SystemV.Terms.Substitution

import SystemV.Evaluation.Values
import SystemV.Evaluation.Casting
import SystemV.Evaluation.Slicing
import SystemV.Evaluation.Reduction

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
progress (TyFunc paramTy returnTy prf) with (progress paramTy)

  progress (TyFunc (Seq left right) returnTy prf) | (Done (Seq x y))
    = Step RewriteTyFuncParam

  progress (TyFunc paramTy returnTy prf) | (Done pvalue) with (progress returnTy)
    progress (TyFunc paramTy (Seq left right) prf) | (Done pvalue) | (Done (Seq x y))
      = Step RewriteTyFuncReturn

    progress (TyFunc paramTy returnTy prf) | (Done pvalue) | (Done rvalue)
      = Done (TyFunc pvalue rvalue)

    progress (TyFunc paramTy returnTy prf) | (Done pvalue) | (Step step)
      = Step (SimplifyTyFuncReturn step)

  progress (TyFunc paramTy returnTy prf) | (Step step)
    = Step (SimplifyTyFuncParam step)

progress TyUnit
  = Done TyUnit

progress (TyNat n)
  = Done TyNat

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

progress (TyTypeDef typeE) with (progress typeE)
  progress (TyTypeDef typeE) | (Done value)
    = Done (TyTypeDef value)

  progress (TyTypeDef typeE) | (Step step)
    = Step (SimplifyTyTypeDef step)

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
  progress (WriteTo (Seq left right)) | (Done (Seq x y))
    = Step RewriteWriteTo
  progress (WriteTo chan) | (Step step)
   = Step (SimplifyWriteTo step)

progress (ReadFrom chan) with (progress chan)
  progress (ReadFrom (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceReadFrom
  progress (ReadFrom (Seq left right)) | (Done (Seq x y))
    = Step RewriteReadFrom
  progress (ReadFrom chan) | (Step step)
   = Step (SimplifyReadFrom step)

progress (Drive chan) with (progress chan)
  progress (Drive (MkPort ty OUT)) | (Done (MkPort tyV OUT))
    = Done (Drive (MkPort tyV OUT))
  progress (Drive (Seq left right)) | (Done (Seq x y))
    = Step RewriteDrive
  progress (Drive chan) | (Step step)
   = Step (SimplifyDrive step)

progress (Catch chan) with (progress chan)
  progress (Catch (MkPort ty IN)) | (Done (MkPort tyV IN))
    = Done (Catch (MkPort tyV IN))
  progress (Catch (Seq left right)) | (Done (Seq x y))
    = Step RewriteCatch

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

  progress (IfThenElseR (Seq left right) whenIsZ whenNotZ) | (Done (Seq x y))
    = Step RewriteCondTest

  progress (IfThenElseR test whenIsZ whenNotZ) | (Step step)
    = Step (SimplifyCondTest step)

-- #### Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) with (progress portR)
    progress (Connect (MkPort tyL dirL) (MkPort tyR dirR) prf) | (Done (MkPort x dirL)) | (Done (MkPort y dirR))
      = Done (Connect (MkPort x dirL) (MkPort y dirR))

    progress (Connect (MkPort tyL dirL) (Seq left right) prf) | (Done (MkPort x dirL)) | (Done (Seq y z))
      = Step RewriteConnectRight

    progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) | (Step step)
      = Step (SimplifyConnectRight step)

  progress (Connect (Seq left right) portR prf) | (Done (Seq x y))
    = Step RewriteConnectLeft

  progress (Connect portL portR prf) | (Step step)
    = Step (SimplifyConnectLeft step)

-- ### Casting & Slicing
progress (Cast portA prf) with (progress portA)
  progress (Cast (MkPort ty dirA) prf) | (Done (MkPort x dirA))
    = Step (ReduceCast (MkPort x dirA))
  progress (Cast (Seq left right) prf) | (Done (Seq x y))
    = Step RewriteCast

  progress (Cast portA prf) | (Step step)
    = Step (SimplifyCast step)

-- #### Slicing

progress (Slice port alpha omega prf) with (progress port)
  progress (Slice (MkPort tyP dir) alpha omega prf) | (Done (MkPort x dir)) with (progress alpha)
    progress (Slice (MkPort tyP dir) (MkNat a) omega prf) | (Done (MkPort x dir)) | (Done MkNat) with (progress omega)
      progress (Slice (MkPort tyP dir) (MkNat a) (MkNat o) prf) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat)
        = Step (ReduceSlice (MkPort x dir))

      progress (Slice (MkPort tyP dir) (MkNat a) (Seq left right) prf) | (Done (MkPort x dir)) | (Done MkNat) | (Done (Seq y z))
        = Step RewriteSliceO

      progress (Slice (MkPort tyP dir) (MkNat a) omega prf) | (Done (MkPort x dir)) | (Done MkNat) | (Step step)
        = Step (SimplifySliceO step)

    progress (Slice (MkPort tyP dir) (Seq left right) omega prf) | (Done (MkPort x dir)) | (Done (Seq y z))
      = Step RewriteSliceA

    progress (Slice (MkPort tyP dir) alpha omega prf) | (Done (MkPort x dir)) | (Step step)
      = Step (SimplifySliceA step)

  progress (Slice (Seq left right) alpha omega prf) | (Done (Seq x y))
    = Step RewriteSlicePort

  progress (Slice port alpha omega prf) | (Step step)
    = Step (SimplifySlicePort step)

-- ### Gates

-- #### Not
progress (Not portO portI) with (progress portO)
  progress (Not (MkPort ty OUT) portI) | (Done (MkPort tyValO OUT)) with (progress portI)

    progress (Not (MkPort tyO OUT) (MkPort tyI IN)) | (Done (MkPort tyValO OUT)) | (Done (MkPort tyVa IN))
      = Done (Not (MkPort tyValO OUT) (MkPort tyVa IN ))

    progress (Not (MkPort tyO OUT) (Seq left right)) | (Done (MkPort tyValO OUT)) | (Done (Seq x y))
      = Step RewriteNotInSeq

    progress (Not (MkPort tyO OUT) portI) | (Done (MkPort tyValO OUT)) | (Step step)
      = Step (SimplifyNotIn step)

  progress (Not (Seq left right) portI) | (Done (Seq x y))
    = Step RewriteNotOutSeq

  progress (Not portO portI) | (Step step)
    = Step (SimplifyNotOut step)

-- #### Binary

progress (Gate kind portO portIA portIB) with (progress portO)
  progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) with (progress portIA)
    progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) with (progress portIB)
      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (MkPort tyIB IN)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (MkPort tyVIB IN))
        = Done (Gate (MkPort tyV OUT) (MkPort tyVIA IN) (MkPort tyVIB IN))

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (Seq left right)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (Seq x y))
        = Step RewriteBinInB

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Step step)
        = Step (SimplifyBinInB step)

    progress (Gate kind (MkPort ty OUT) (Seq left right) portIB) | (Done (MkPort tyV OUT)) | (Done (Seq x y))
      = Step RewriteBinInA

    progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) | (Step step)
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

progress (MkNat n)
  = Done MkNat

-- [ EOF ]
