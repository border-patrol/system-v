module SystemV.Params.Evaluation.Progress

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms


import SystemV.Params.Terms.Renaming
import SystemV.Params.Terms.Substitution

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden
import SystemV.Params.Evaluation.Connecting
import SystemV.Params.Evaluation.Casting
import SystemV.Params.Evaluation.Slicing

import SystemV.Params.Evaluation.Indexing
import SystemV.Params.Evaluation.Sizing
import SystemV.Params.Evaluation.Comparing
import SystemV.Params.Evaluation.Arith

import SystemV.Params.Evaluation.Reduction

%hide Alt.Overridden
%hide Alt.overridden

%default total

public export
data Progress : (err  : Type)
             -> (term : SystemV Nil type)
                     -> Type
  where
    Done : forall mty . {term  : SystemV Nil mty}
                     -> (value : Value term)
                              -> Progress err term

    Step : {this, that : SystemV Nil type}
        -> (step       : Redux this that)
                      -> Progress err this

    Halt : forall mty . {term : SystemV Nil mty}
                     -> (msg  : err)
                             -> Progress err term


data Error = DivZero
           | NotAVector
           | InvalidCast
           | InvalidSlice
           | InvalidConnect
           | InvalidIndex
           | InvalidCmp

{-
  public export
  data Error = Err FileContext Build.Error
             | NotAName String
             | TypeMismatch (TYPE a) (TYPE b)
             | VectorSizeZero
             | IndexOutOfBounds Nat Whole
             | WrongType Context (TYPE a)
             | InvalidCast Cast.Error (TYPE (IDX TERM)) (TYPE (IDX TERM))
             | InvalidBound Sliceable.Error
             | InvalidFlow  Flow.Error
             | InvalidFuncSynth Synthesis.Error (TYPE a)
             | InvalidFunc Function.ValidTerm.Error (TYPE a) (TYPE b)
-}
public export
progress : (term : SystemV Nil type)
                -> Progress Progress.Error term

-- ### STLC with Defaults Types

progress (TyFunc paramTy returnTy vld) with (progress paramTy)
  progress (TyFunc (Seq l r) returnTy vld) | (Done (Seq u v))
    = Step RewriteTyFuncParam

  progress (TyFunc paramTy returnTy vld) | (Done p) with (progress returnTy)
    progress (TyFunc paramTy (Seq l r) vld) | (Done p) | (Done (Seq u v))
      = Step RewriteTyFuncReturn

    progress (TyFunc paramTy returnTy vld) | (Done p) | (Done r)
      = Done (TyFunc p r)

    progress (TyFunc paramTy returnTy vld) | (Done p) | (Step step)
      = Step (SimplifyTyFuncReturn step)

    progress (TyFunc paramTy returnTy vld) | (Done p) | (Halt msg)
      = Halt msg

  progress (TyFunc paramTy returnTy vld) | (Step step)
    = Step (SimplifyTyFuncParam step)

  progress (TyFunc paramTy returnTy vld) | (Halt msg)
    = Halt msg

progress (TyFuncD paramTy returnTy vld) with (progress paramTy)
  progress (TyFuncD (Seq l r) returnTy vld) | (Done (Seq u v))
    = Step RewriteTyFuncDParam

  progress (TyFuncD paramTy returnTy vld) | (Done p) with (progress returnTy)
    progress (TyFuncD paramTy (Seq l r) vld) | (Done p) | (Done (Seq u v))
      = Step RewriteTyFuncDReturn

    progress (TyFuncD paramTy returnTy vld) | (Done p) | (Done r)
      = Done (TyFuncD p r)

    progress (TyFuncD paramTy returnTy vld) | (Done p) | (Step step)
      = Step (SimplifyTyFuncDReturn step)

    progress (TyFuncD paramTy returnTy vld) | (Done p) | (Halt msg)
      = Halt msg

  progress (TyFuncD paramTy returnTy vld) | (Step step)
    = Step (SimplifyTyFuncDParam step)

  progress (TyFuncD paramTy returnTy vld) | (Halt msg)
    = Halt msg

-- ### Construction Types

progress TyUnit
  = Done TyUnit

progress (TyNat n)
  = Done TyNat

progress TyBool
  = Done TyBool

-- ### Hardware Types

progress TyModule
  = Done TyModule

progress (TyChan typeD) with (progress typeD)

  progress (TyChan typeD) | (Done value)
    = Done (TyChan value)

  progress (TyChan typeD) | (Step step)
    = Step (SimplifyTyChan step)

  progress (TyChan typeD) | (Halt err)
    = Halt err

progress (TyPort typeD dir) with (progress typeD)

  progress (TyPort typeD dir) | (Done value)
    = Done (TyPort value dir)

  progress (TyPort typeD dir) | (Step step)
    = Step (SimplifyTyPort step)

  progress (TyPort typeD dir) | (Halt err)
    = Halt err

-- ### Data Types

progress (TyTypeDef typeE) with (progress typeE)
  progress (TyTypeDef typeE) | (Done value)
    = Done (TyTypeDef value)

  progress (TyTypeDef typeE) | (Step step)
    = Step (SimplifyTyTypeDef step)

  progress (TyTypeDef typeE) | (Halt err)
    = Halt err

progress TyLogic
  = Done TyLogic

progress (TyVect s typeE) with (progress typeE)
  progress (TyVect s typeE) | (Done value)
    = Done (TyVect s value)

  progress (TyVect s typeE) | (Step step)
    = Step (SimplifyTyVect step)

  progress (TyVect s typeE) | (Halt err)
    = Halt err

progress (TyOverride inner) with (progress inner)
  progress (TyOverride typeE) | (Done value)
    = Done (TyOverride value)

  progress (TyOverride typeE) | (Step step)
    = Step (SimplifyTyOverride step)

  progress (TyOverride typeE) | (Halt err)
    = Halt err

-- ## Terms

-- ### STLC with Defaults

progress (Var idx) impossible

progress (Func x body prf vld) = ?progress_rhs_14
progress (FuncD x def body prf vld) = ?progress_rhs_15

progress (App func value) = ?progress_rhs_16
progress (AppDef func) = ?progress_rhs_17
progress (AppOver func param) = ?progress_rhs_18

-- ### Hardware specific

progress MkUnit
  = Done MkUnit

progress EndModule
  = Done EndModule

-- #### Ports

progress (MkPort typeD dir) with (progress typeD)
  progress (MkPort typeD dir) | (Done value)
    = Done (MkPort value dir)

  progress (MkPort typeD dir) | (Step step)
    = Step (SimplifyMkPort step)

  progress (MkPort typeD dir) | (Halt msg)
    = Halt msg

-- #### Channels

progress (MkChan typeD) with (progress typeD)
  progress (MkChan typeD) | Done value
    = Done (MkChan value)
  progress (MkChan typeD) | (Step step)
    = Step (SimplifyMkChan step)
  progress (MkChan typeD) | Halt msg
    = Halt msg

-- ##### Projection
progress (WriteTo chan) with (progress chan)
  progress (WriteTo (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceWriteTo
  progress (WriteTo (Seq left right)) | (Done (Seq x y))
    = Step RewriteWriteTo
  progress (WriteTo chan) | (Step step)
    = Step (SimplifyWriteTo step)
  progress (WriteTo chan) | (Halt msg)
    = Halt msg

progress (ReadFrom chan) with (progress chan)
  progress (ReadFrom (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceReadFrom
  progress (ReadFrom (Seq left right)) | (Done (Seq x y))
    = Step RewriteReadFrom
  progress (ReadFrom chan) | (Step step)
    = Step (SimplifyReadFrom step)
  progress (ReadFrom chan) | (Halt msg)
    = Halt msg

-- ##### Termination
-- ###### Driving
progress (Drive chan) with (progress chan)
  progress (Drive (MkPort ty OUT)) | (Done (MkPort tyV OUT))
    = Done (Drive (MkPort tyV OUT))

  progress (Drive (Seq left right)) | (Done (Seq x y))
    = Step RewriteDrive

  progress (Drive chan) | (Step step)
   = Step (SimplifyDrive step)

  progress (Drive chan) | (Halt msg)
   = Halt msg

-- ###### Catching

progress (Catch chan) with (progress chan)
  progress (Catch (MkPort ty IN)) | (Done (MkPort tyV IN))
    = Done (Catch (MkPort tyV IN))

  progress (Catch (Seq left right)) | (Done (Seq x y))
    = Step RewriteCatch

  progress (Catch chan) | (Step step)
   = Step (SimplifyCatch step)

  progress (Catch chan) | (Halt msg)
   = Halt msg

-- #### Runtime wiring decisions
progress (IfThenElseR test whenIsZ whenNotZ) with (progress test)
  progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) with (progress whenIsZ)
    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) with (progress whenNotZ)
      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Done false)
        = Done (IfThenElseR (MkPort tyV IN) true false)

      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Step step)
        = Step (SimplifyCondFalse step)

      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | Halt msg
        = Halt msg

    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Step step)
      = Step (SimplifyCondTrue step)

    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Halt msg)
      = Halt msg

  progress (IfThenElseR (Seq left right) whenIsZ whenNotZ) | (Done (Seq x y))
    = Step RewriteCondTest

  progress (IfThenElseR test whenIsZ whenNotZ) | (Step step)
    = Step (SimplifyCondTest step)

  progress (IfThenElseR test whenIsZ whenNotZ) | (Halt msg)
    = Halt msg

-- #### Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort tyLV dirL)) with (progress portR)
      progress (Connect (MkPort tyL dirL) (MkPort tyR dirR) prf) | (Done (MkPort tyLV dirL)) | (Done (MkPort tyRV dirR)) with (canConnect tyLV tyRV)
        progress (Connect (MkPort tyL dirL) (MkPort tyR dirR) prf) | (Done (MkPort tyLV dirL)) | (Done (MkPort tyRV dirR)) | Nothing
          = Halt InvalidConnect
        progress (Connect (MkPort tyL dirL) (MkPort tyR dirR) prf) | (Done (MkPort tyLV dirL)) | (Done (MkPort tyRV dirR)) | (Just x)
          = Done (Connect (MkPort tyLV dirL) (MkPort tyRV dirR))

      progress (Connect (MkPort tyL dirL) (Seq left right) prf) | (Done (MkPort tyLV dirL)) | (Done (Seq x y))
        = Step RewriteConnectRight

      progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort tyLV dirL)) | (Step step)
        = Step (SimplifyConnectRight step)

      progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort tyLV dirL)) | (Halt msg)
        = Halt msg

  progress (Connect (Seq left right) portR prf) | (Done (Seq x y))
    = Step RewriteConnectLeft


  progress (Connect portL portR prf) | (Step step)
    = Step (SimplifyConnectLeft step)

  progress (Connect portL portR prf) | (Halt msg)
    = Halt msg


-- #### Casting

progress (Cast portA prf {tyB} {dirB}) with (progress portA)
  progress (Cast (MkPort tyA dirA) prf {tyB = tyB} {dirB = dirB}) | (Done (MkPort tyAVal dirA)) with (overridden tyAVal)

    progress (Cast (MkPort (TyOverride term) dirA) prf {tyB = tyB} {dirB = dirB}) | (Done (MkPort (TyOverride val) dirA)) | (Yes (IsOverridden x term val)) with (validCast (PortTy x dirA) (PortTy tyB dirB))
      progress (Cast (MkPort (TyOverride term) dirA) prf {tyB = tyB} {dirB = dirB}) | (Done (MkPort (TyOverride val) dirA)) | (Yes (IsOverridden x term val)) | (Yes prfWhy)
        = Step (ReduceCastOverride val prfWhy)

      progress (Cast (MkPort (TyOverride term) dirA) prf {tyB = tyB} {dirB = dirB}) | (Done (MkPort (TyOverride val) dirA)) | (Yes (IsOverridden x term val)) | (No msgWhyNot prfWhyNot)
        = Halt InvalidCast

    progress (Cast (MkPort tyA dirA) prf {  tyB = tyB} {  dirB = dirB}) | (Done (MkPort tyAVal dirA)) | (No contra)
      = Step (ReduceCast (MkPort tyAVal dirA))

  progress (Cast (Seq left right) prf {tyB = tyB} {  dirB = dirB}) | (Done (Seq x y))
    = Step RewriteCast

  progress (Cast portA prf {tyB = tyB} {dirB = dirB}) | (Step step)
    = Step (SimplifyCast step)

  progress (Cast portA prf {tyB = tyB} {dirB = dirB}) | (Halt msg)
    = Halt msg


-- #### Slicing

progress (Slice port alpha omega prf) with (progress port)
  progress (Slice (MkPort t dir) alpha omega prf) | (Done (MkPort v dir)) with (progress alpha)
    progress (Slice (MkPort t dir) (Seq left right) omega prf) | (Done (MkPort v dir)) | (Done (Seq x y))
      = Step RewriteSliceA

    progress (Slice (MkPort t dir) tA omega prf) | (Done (MkPort v dir)) | (Done vA) with (progress omega)
      progress (Slice (MkPort t dir) tA (Seq left right) prf) | (Done (MkPort v dir)) | (Done vA) | (Done (Seq x y))
        = Step RewriteSliceO

      progress (Slice (MkPort t dir) tA tO prf) | (Done (MkPort v dir)) | (Done vA) | (Done vO) with (validArgs (MkPort t dir) (MkPort v dir) tA vA tO vO)
        progress (Slice (MkPort t dir) tA tO prf) | (Done (MkPort v dir)) | (Done vA) | (Done vO) | Nothing
          = Halt InvalidSlice

        progress (Slice (MkPort t dir) tA tO prf) | (Done (MkPort v dir)) | (Done vA) | (Done vO) | (Just x)
          = Step (ReduceSlice (MkPort v dir) vA vO x)


      progress (Slice (MkPort t dir) tA omega prf) | (Done (MkPort v dir)) | (Done vA) | (Step step)
        = Step (SimplifySliceO step)

      progress (Slice (MkPort t dir) tA omega prf) | (Done (MkPort v dir)) | (Done vA) | (Halt msg)
        = Halt msg

    progress (Slice (MkPort t dir) alpha omega prf) | (Done (MkPort v dir)) | (Step step)
      = Step (SimplifySliceA step)

    progress (Slice (MkPort t dir) alpha omega prf) | (Done (MkPort v dir)) | (Halt msg)
      = Halt msg

  progress (Slice (Seq left right) alpha omega prf) | (Done (Seq x y))
    = Step RewriteSlicePort

  progress (Slice port alpha omega prf) | (Step step)
    = Step (SimplifySlicePort step)

  progress (Slice port alpha omega prf) | (Halt msg)
    = Halt msg

-- #### Indexing

progress (Index idx port prf) with (progress idx)

  progress (Index (Seq left right) port prf) | (Done (Seq x y))
    = Step RewriteIndexI

  progress (Index idx port prf) | (Done value) with (progress port)
    progress (Index idx (MkPort ty dir) prf) | (Done value) | (Done (MkPort x dir)) with (validArgs idx value (MkPort ty dir) (MkPort x dir))
      progress (Index idx (MkPort ty dir) prf) | (Done value) | (Done (MkPort x dir)) | Nothing
        = Halt InvalidIndex
      progress (Index idx (MkPort ty dir) prf) | (Done value) | (Done (MkPort x dir)) | (Just y)
        = Step (ReduceIndex value (MkPort x dir) y)
    progress (Index idx (Seq left right) prf) | (Done value) | (Done (Seq x y))
      = Step RewriteIndexPort

    progress (Index idx port prf) | (Done value) | (Step step)
      = Step (SimplifyIndexPort value step)
    progress (Index idx port prf) | (Done value) | (Halt msg)
      = Halt msg

  progress (Index idx port prf) | (Step step)
    = Step (SimplifyIndexI step)
  progress (Index idx port prf) | (Halt msg)
    = Halt msg

-- #### Sizing

progress (Size port) with (progress port)

  progress (Size (Seq left right)) | (Done (Seq x y))
    = Step RewriteSize

  progress (Size port) | (Done value) with (Sizing.validArgs port value)
    progress (Size port) | (Done value) | Nothing
      = Halt NotAVector
    progress (Size port) | (Done value) | (Just x)
      = Step (ReduceSize value x)

  progress (Size port) | Step step
    = Step (SimplifySize step)

  progress (Size port) | Halt msg
    = Halt msg


-- #### Gates

-- ##### Not
progress (Not portO portI) = ?progress_rhs_33

-- ##### Binary
progress (Gate kind portO portIA portIB) = ?progress_rhs_34

-- #### Structure
progress (Let value body) = ?progress_rhs_35
progress (Seq left right) = ?progress_rhs_36

-- #### Nats

progress (MkNat n)
  = Done MkNat

progress (NatOverride n)
  = Done NatOverride

progress (OpArith op left right) = ?progress_rhs_39

-- #### Bools

-- ##### Values
progress (B x)
  = Done B

-- ##### Bool Ops
progress (OpBool op left right) with (progress left)
  progress (OpBool op (B l) right) | Done B with (progress right)
    progress (OpBool op (B l) (B r)) | Done B | Done B
      = Step ReduceOpBool

    progress (OpBool op (B l) (Seq left right)) | Done B | Done (Seq x y)
      = Step RewriteOpBoolR

    progress (OpBool op (B l) right) | Done B | Step step
      = Step (SimplifyOpBoolR B step)

    progress (OpBool op (B l) right) | Done B | Halt msg
      = Halt msg

  progress (OpBool op (Seq l rightr) right) | Done (Seq x y)
    = Step RewriteOpBoolL

  progress (OpBool op left right) | Step step
    = Step (SimplifyOpBoolL step)

  progress (OpBool op left right) | Halt msg
    = Halt msg

-- ##### Nat Cmp
progress (OpCmp op left right) with (progress left)
  progress (OpCmp op (Seq l r) right) | Done (Seq x y)
    = Step RewriteOpCmpL

  progress (OpCmp op left right) | Done vl with (progress right)
    progress (OpCmp op left (Seq l r)) | Done vl | Done (Seq x y)
      = Step RewriteOpCmpR

    progress (OpCmp op left right) | Done vl | Done vr with (Comparing.validArgs left vl right vr)
      progress (OpCmp op left right) | Done vl | Done vr | Nothing
        = Halt InvalidCmp
      progress (OpCmp op left right) | Done vl | Done vr | (Just x)
        = Step (ReduceOpCmp vl vr x)

    progress (OpCmp op left right) | Done vl | Step step
      = Step (SimplifyOpCmpR vl step)

    progress (OpCmp op left right) | Done vl | Halt msg
      = Halt msg

  progress (OpCmp op left right) | Step step
    = Step (SimplifyOpCmpL step)

  progress (OpCmp op left right) | Halt msg
    = Halt msg

-- ##### Not
progress (OpNot bool) with (progress bool)
  progress (OpNot bool) | (Done value) with (value)
    progress (OpNot (B True)) | (Done value) | B
      = Step ReduceOpNotT
    progress (OpNot (B False)) | (Done value) | B
      = Step ReduceOpNotF

    progress (OpNot (Seq left right)) | (Done value) | (Seq x y)
      = Step RewriteOpNot

  progress (OpNot bool) | (Step step)
    = Step (SimplifyOpNot step)

  progress (OpNot bool) | (Halt msg)
    = Halt msg
progress (IfThenElseC test whenT whenF) = ?progress_rhs_42


{-

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

-- ### Sizing

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
-}
-- [ EOF ]
