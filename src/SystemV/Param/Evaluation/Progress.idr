module SystemV.Param.Evaluation.Progress

import Toolkit.Decidable.Equality.Views

import SystemV.Common.Utilities
import SystemV.Param.Types
import SystemV.Param.Terms


import SystemV.Param.Terms.Renaming
import SystemV.Param.Terms.Substitution

import SystemV.Param.Evaluation.Error
import SystemV.Param.Evaluation.Values

import SystemV.Param.Evaluation.Casting
import SystemV.Param.Evaluation.Slicing

import SystemV.Param.Evaluation.Equality
import SystemV.Param.Evaluation.Check

import SystemV.Param.Evaluation.Reduction

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

    Halt : {term   : SystemV Nil type}
        -> (reason : Param.Evaluation.Error)
                  -> Progress term

export
progress : (term : SystemV Nil type)
        -> Progress term

-- [ Types ]
progress DATATYPE
  = Done DATATYPE

progress TyUnit
  = Done TyUnit

progress TyModule
  = Done TyModule

progress TyNat
  = Done TyNat

progress TyBool
  = Done TyBool

progress (TyChan typeD) with (progress typeD)
  progress (TyChan typeD) | (Done value)
    = Done (TyChan value)
  progress (TyChan typeD) | (Step step)
    = Step (SimplifyTyChan step)
  progress (TyChan typeD) | Halt err
    = Halt err

progress (TyPort typeD dir) with (progress typeD)
  progress (TyPort typeD dir) | (Done value)
    = Done (TyPort value dir)
  progress (TyPort typeD dir) | (Step step)
    = Step (SimplifyTyPort step)
  progress (TyPort typeD dir) | (Halt err)
    = Halt err

progress TyLogic
  = Done TyLogic

progress (TyVect s typeE) with (progress s)
  progress (TyVect (MkNat n) typeE) | (Done MkNat) with (progress typeE)
    progress (TyVect (MkNat n) typeE) | (Done MkNat) | (Done value) with (isItSucc n)
      progress (TyVect (MkNat (S n)) typeE) | (Done MkNat) | (Done value) | (Yes ItIsSucc)
        = Done (TyVect value ItIsSucc)
      progress (TyVect (MkNat n) typeE) | (Done MkNat) | (Done value) | (No contra)
        = Halt VectorCannotBeZero

    progress (TyVect (MkNat n) typeE) | (Done MkNat) | (Step step)
      = Step (SimplifyTyVectType step)
    progress (TyVect (MkNat n) typeE) | (Done MkNat) | (Halt reason)
      = Halt reason

  progress (TyVect (Seq left right) typeE) | (Done (Seq x y))
    = Halt UnexpectedSeq

  progress (TyVect s typeE) | (Step step)
    = Step (SimplifyTyVectSize step)
  progress (TyVect s typeE) | (Halt reason)
    = Halt reason

-- [ Terms ]

-- ### STLC


progress (Func x body prf vld) = Done Func

progress (App func param) with (progress func)
  progress (App (Func ty body prf vld) param) | (Done Func) with (progress param)

    progress (App (Func ty body prf vld) param) | (Done Func) | (Done value) with (progress ty)
      progress (App (Func ty body prf vld) param) | (Done Func) | (Done value) | (Done tyV) with (check ty tyV param value prf vld)
        progress (App (Func ty body prf vld) param) | (Done Func) | (Done value) | (Done tyV) | Left err
          = case err of
             UnexpectedSeq => Halt UnexpectedSeq
             TypeMismatch a b => Halt (TypeMismatch a b)
        progress (App (Func ty body prf vld) param) | (Done Func) | (Done value) | (Done tyV) | (Right x)
          = Step (ReduceFunc tyV value x {body=body})
      progress (App (Func ty body prf vld) param) | (Done Func) | (Done value) | (Step step)
        = Step (SimplifyFuncAppType step)
      progress (App (Func ty body prf vld) param) | (Done Func) | (Done value) | (Halt reason)
        = Halt reason

    progress (App (Func ty body prf vld) param) | (Done Func) | (Step step)
      = Step (SimplifyFuncAppVar Func step)

    progress (App (Func ty body prf vld) param) | (Done Func) | (Halt err)
      = Halt err

  progress (App (Seq left right) param) | (Done (Seq x y))
    = Step RewriteFuncAppFunc

  progress (App func param) | (Step step)
    = Step (SimplifyFuncAppFunc step)

  progress (App func param) | (Halt err)
    = Halt err

-- #### Paramterised Functions
progress (FuncParam x def body prf chk) = Done (FuncP chk)

-- #### App Override

progress (AppOver func var) with (progress func)
  progress (AppOver (FuncParam ty def body prf chk) var) | (Done (FuncP chk)) with (progress var)
    progress (AppOver (FuncParam ty def body prf chk) var) | (Done (FuncP chk)) | (Done value)
      = Step ReduceAppOver

    progress (AppOver (FuncParam ty def body prf chk) var) | (Done (FuncP chk)) | (Step step)
      = Step (SimplifyAppOverVar (FuncP chk) step)

    progress (AppOver (FuncParam ty def body prf chk) var) | (Done (FuncP chk)) | (Halt reason)
      = Halt reason

  progress (AppOver (Seq left right) var) | (Done (Seq x y))
    = Step RewriteAppOverFun

  progress (AppOver func var) | (Step step)
    = Step (SimplifyAppOverFun step)

  progress (AppOver func var) | (Halt reason)
    = Halt reason

-- #### Application Default
progress (AppDef func) with (progress func)
  progress (AppDef (FuncParam ty def body prf chk)) | Done (FuncP chk)
    = Step ReduceAppDef

  progress (AppDef (Seq l r)) | Done (Seq u v)
    = Step RewriteAppDef

  progress (AppDef func) | Step step
    = Step (SimplifyAppDef step)

  progress (AppDef func) | Halt reason
    = Halt reason

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

  progress (MkPort typeD dir) | (Halt err)
    = Halt err

-- ### Channels

progress (MkChan typeD) with (progress typeD)
  progress (MkChan typeD) | (Done value)
    = Done (MkChan value)

  progress (MkChan typeD) | (Step step)
    = Step (SimplifyMkChan step)

  progress (MkChan typeD) | (Halt err)
    = Halt err

progress (WriteTo chan) with (progress chan)
  progress (WriteTo (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceWriteTo
  progress (WriteTo (Seq left right)) | (Done (Seq x y))
    = Step RewriteWriteTo
  progress (WriteTo chan) | (Step step)
   = Step (SimplifyWriteTo step)
  progress (WriteTo chan) | (Halt err)
    = Halt err

progress (ReadFrom chan) with (progress chan)
  progress (ReadFrom (MkChan port)) | (Done (MkChan portVal))
    = Step ReduceReadFrom
  progress (ReadFrom (Seq left right)) | (Done (Seq x y))
    = Step RewriteReadFrom
  progress (ReadFrom chan) | (Step step)
    = Step (SimplifyReadFrom step)
  progress (ReadFrom chan) | (Halt err)
    = Halt err

progress (Drive chan) with (progress chan)
  progress (Drive (MkPort ty OUT)) | (Done (MkPort tyV OUT))
    = Done (Drive (MkPort tyV OUT))
  progress (Drive (Seq left right)) | (Done (Seq x y))
    = Step RewriteDrive
  progress (Drive chan) | (Step step)
    = Step (SimplifyDrive step)
  progress (Drive chan) | (Halt err)
    = Halt err

progress (Catch chan) with (progress chan)
  progress (Catch (MkPort ty IN)) | (Done (MkPort tyV IN))
    = Done (Catch (MkPort tyV IN))

  progress (Catch (Seq left right)) | (Done (Seq x y))
    = Step RewriteCatch

  progress (Catch chan) | (Step step)
   = Step (SimplifyCatch step)

  progress (Catch chan) | (Halt err)
   = Halt err

-- ### Decisions & Connections
progress (IfThenElseR test whenIsZ whenNotZ) with (progress test)
  progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) with (progress whenIsZ)
    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) with (progress whenNotZ)
      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Done false)
        = Done (IfThenElseR (MkPort tyV IN) true false)

      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Step step)
        = Step (SimplifyCondFalse step)

      progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Halt err)
        = Halt err

    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Step step)
      = Step (SimplifyCondTrue step)

    progress (IfThenElseR (MkPort ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Halt err)
      = Halt err

  progress (IfThenElseR (Seq left right) whenIsZ whenNotZ) | (Done (Seq x y))
    = Step RewriteCondTest

  progress (IfThenElseR test whenIsZ whenNotZ) | (Step step)
    = Step (SimplifyCondTest step)

  progress (IfThenElseR test whenIsZ whenNotZ) | (Halt err)
    = Halt err

-- #### Connections
progress (Connect portL portR prf) with (progress portL)
  progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) with (progress portR)
    progress (Connect (MkPort tyL dirL) (MkPort tyR dirR) prf) | (Done (MkPort x dirL)) | (Done (MkPort y dirR))
      = case decEq tyL x tyR y of
          No c => Halt (TypeMismatch tyL tyR)
          Yes Refl => Done (Connect (MkPort x dirL) (MkPort y dirR))

    progress (Connect (MkPort tyL dirL) (Seq left right) prf) | (Done (MkPort x dirL)) | (Done (Seq y z))
      = Step RewriteConnectRight

    progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) | (Step step)
      = Step (SimplifyConnectRight step)

    progress (Connect (MkPort tyL dirL) portR prf) | (Done (MkPort x dirL)) | (Halt err)
      = Halt err

  progress (Connect (Seq left right) portR prf) | (Done (Seq x y))
    = Step RewriteConnectLeft

  progress (Connect portL portR prf) | (Step step)
    = Step (SimplifyConnectLeft step)

  progress (Connect portL portR prf) | (Halt err)
    = Halt err

-- ### Casting & Slicing
progress (Cast portA type dir prf) with (progress portA)
  progress (Cast (MkPort ty dirA) type dir prf) | (Done (MkPort x dirA)) with (progress type)
    progress (Cast (MkPort ty dirA) type dir prf) | (Done (MkPort x dirA)) | (Done value)
      = case checkCast prf (MkPort ty dirA) (MkPort x dirA) type value of
          Left err =>
             case err of
               UnexpectedSeq => Halt UnexpectedSeq
               TypeMismatch a b => Halt (TypeMismatch a b)
          Right prfC => Step (ReduceCast (MkPort x dirA) value prfC)
    progress (Cast (MkPort ty dirA) type dir prf) | (Done (MkPort x dirA)) | (Step step)
      = Step (SimplifyCastType step)
    progress (Cast (MkPort ty dirA) type dir prf) | (Done (MkPort x dirA)) | (Halt reason)
      = Halt reason

  progress (Cast (Seq left right) type dir prf) | (Done (Seq x y))
    = Step RewriteCastPort

  progress (Cast portA type dir prf) | (Step step)
    = Step (SimplifyCastPort step)

  progress (Cast portA type dir prf) | (Halt err)
    = Halt err

-- #### Slicing

progress (Slice port alpha omega) with (progress port)
  progress (Slice (MkPort tyP dir) alpha omega) | (Done (MkPort x dir)) with (progress alpha)
    progress (Slice (MkPort tyP dir) (MkNat a) omega) | (Done (MkPort x dir)) | (Done MkNat) with (progress omega)
      progress (Slice (MkPort tyP dir) (MkNat a) (MkNat o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) with (x)
        progress (Slice (MkPort (TyVect (MkNat s) ty) dir) (MkNat a) (MkNat o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | (TyVect y z) with (validBound a o (W s z))
          progress (Slice (MkPort (TyVect (MkNat s) ty) dir) (MkNat a) (MkNat o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | (TyVect y z) | (Yes prfWhy)
            = Step (ReduceSlice z prfWhy)
          progress (Slice (MkPort (TyVect (MkNat s) ty) dir) (MkNat a) (MkNat o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | (TyVect y z) | (No msgWhyNot prfWhyNot)
            = Halt (InvalidBound msgWhyNot)
        progress (Slice (MkPort TyLogic dir) (MkNat a) (MkNat o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | TyLogic
          = Halt ExpectedVector
      progress (Slice (MkPort tyP dir) (MkNat a) (Seq l r)) | (Done (MkPort x dir)) | (Done MkNat) | (Done (Seq x' y))
        = Step RewriteSliceOmega

      progress (Slice (MkPort tyP dir) (MkNat a) omega) | (Done (MkPort x dir)) | (Done MkNat) | (Step step)
        = Step (SimplifySliceOmega step)
      progress (Slice (MkPort tyP dir) (MkNat a) omega) | (Done (MkPort x dir)) | (Done MkNat) | (Halt reason)
        = Halt reason

    progress (Slice (MkPort tyP dir) (Seq l r) omega) | (Done (MkPort x dir)) | (Done (Seq x' y))
      = Step RewriteSliceAlpha


    progress (Slice (MkPort tyP dir) alpha omega) | (Done (MkPort x dir)) | (Step step)
      = Step (SimplifySliceAlpha step)
    progress (Slice (MkPort tyP dir) alpha omega) | (Done (MkPort x dir)) | (Halt reason)
      = Halt reason

  progress (Slice (Seq left right) alpha omega) | (Done (Seq x y))
    = Step RewriteSlicePort

  progress (Slice port alpha omega) | (Step step)
    = Step (SimplifySlicePort step)

  progress (Slice port alpha omega) | (Halt err)
    = Halt err

-- #### Indexing
progress (Index n port)  with (progress port)
  progress (Index n (MkPort ty dir)) | (Done (MkPort tyV dir)) with (progress n)
    progress (Index (MkNat n) (MkPort ty dir)) | (Done (MkPort tyV dir)) | (Done MkNat) with (tyV)
      progress (Index (MkNat n) (MkPort (TyVect (MkNat s) ty) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | (TyVect x y) with (isLTE (S n) s)
        progress (Index (MkNat n) (MkPort (TyVect (MkNat s) ty) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | (TyVect x y) | (Yes prf)
          = Step (ReduceIndex prf)
        progress (Index (MkNat n) (MkPort (TyVect (MkNat s) ty) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | (TyVect x y) | (No contra)
          = Halt (IndexOutOfBounds n (W s y))
      progress (Index (MkNat n) (MkPort TyLogic dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | TyLogic
        = Halt ExpectedVector
    progress (Index (Seq l r) (MkPort ty dir)) | (Done (MkPort tyV dir)) | (Done (Seq x y))
      = Step RewriteIndexIdx

    progress (Index n (MkPort ty dir)) | (Done (MkPort tyV dir)) | (Step step)
      = Step (SimplifyIndexIdx step)
    progress (Index n (MkPort ty dir)) | (Done (MkPort tyV dir)) | (Halt reason)
      = Halt reason

  progress (Index n (Seq left right)) | (Done (Seq x y))
    = Step RewriteIndexPort

  progress (Index n port) | (Step step)
    = Step (SimplifyIndexPort step)

  progress (Index n port) | (Halt err)
    = Halt err

-- #### Size

progress (Size port) with (progress port)
  progress (Size (MkPort ty dir)) | (Done (MkPort tyV dir)) with (tyV)
    progress (Size (MkPort TyLogic dir)) | (Done (MkPort tyV dir)) | TyLogic
      = Halt ExpectedVector
    progress (Size (MkPort (TyVect (MkNat s) ty) dir)) | (Done (MkPort tyV dir)) | (TyVect x y)
      = Step (ReduceSize)

  progress (Size (Seq left right)) | (Done (Seq x y))
    = Step RewriteSize

  progress (Size port) | (Step step)
    = Step (SimplifySizePort step)
  progress (Size port) | (Halt reason)
    = Halt reason

-- ### Gates

-- #### Not
progress (Not portO portI) with (progress portO)
  progress (Not (MkPort ty OUT) portI) | (Done (MkPort tyValO OUT)) with (progress portI)

    progress (Not (MkPort tyO OUT) (MkPort tyI IN)) | (Done (MkPort tyValO OUT)) | (Done (MkPort tyVa IN))
      = case decEq tyO tyValO tyI tyVa of
          Yes Refl => Done (Not (MkPort tyValO OUT) (MkPort tyVa IN ))
          No contra => Halt (TypeMismatch tyO tyI)

    progress (Not (MkPort tyO OUT) (Seq left right)) | (Done (MkPort tyValO OUT)) | (Done (Seq x y))
      = Step RewriteNotInSeq

    progress (Not (MkPort tyO OUT) portI) | (Done (MkPort tyValO OUT)) | (Step step)
      = Step (SimplifyNotIn step)

    progress (Not (MkPort tyO OUT) portI) | (Done (MkPort tyValO OUT)) | (Halt err)
      = Halt err

  progress (Not (Seq left right) portI) | (Done (Seq x y))
    = Step RewriteNotOutSeq

  progress (Not portO portI) | (Step step)
    = Step (SimplifyNotOut step)

  progress (Not portO portI) | (Halt err)
    = Halt err

-- #### Binary

progress (Gate kind portO portIA portIB) with (progress portO)
  progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) with (progress portIA)
    progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) with (progress portIB)
      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (MkPort tyIB IN)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (MkPort tyVIB IN))
        = case decEq ty tyV tyIA tyVIA of
            No c => Halt (TypeMismatch ty tyIA)
            Yes Refl =>
              case decEq ty tyV tyIB tyVIB of
                No c => Halt (TypeMismatch ty tyIB)
                Yes Refl => Done (Gate (MkPort tyV OUT) (MkPort tyVIA IN) (MkPort tyVIB IN))

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) (Seq left right)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (Seq x y))
        = Step RewriteBinInB

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Step step)
        = Step (SimplifyBinInB step)

      progress (Gate kind (MkPort ty OUT) (MkPort tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Halt err)
        = Halt err

    progress (Gate kind (MkPort ty OUT) (Seq left right) portIB) | (Done (MkPort tyV OUT)) | (Done (Seq x y))
      = Step RewriteBinInA

    progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) | (Step step)
      = Step (SimplifyBinInA step)

    progress (Gate kind (MkPort ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) | (Halt err)
      = Halt err

  progress (Gate kind (Seq left right) portIA portIB) | (Done (Seq x y))
    = Step RewriteBinOut

  progress (Gate kind portO portIA portIB) | (Step step)
    = Step (SimplifyBinOut step)

  progress (Gate kind portO portIA portIB) | (Halt err)
    = Halt err

-- ### Binders
progress (Let value body) with (progress value)
  progress (Let value body) | (Done val)
    = Step (ReduceLetBody val)

  progress (Let value body) | (Step step)
    = Step (SimplifyLetValue step)

  progress (Let value body) | (Halt err)
    = Halt err

-- ### Sequencing
progress (Seq left right) with (progress left)

  progress (Seq (Seq x y) right) | (Done (Seq xVal yVal))
    = Step RewriteSeq

  progress (Seq left right) | (Done leftVal) with (progress right)
    progress (Seq left right) | (Done leftVal) | (Done rightVal)
      = Done (Seq leftVal rightVal)

    progress (Seq left right) | (Done leftVal) | (Step step)
      = Step (SimplifySeqRight leftVal step)

    progress (Seq left right) | (Done leftVal) | (Halt err)
      = Halt err

  progress (Seq left right) | (Step step)
    = Step (SimplifySeqLeft step)

  progress (Seq left right) | (Halt err)
    = Halt err
-- ### Nats & Bools

progress (MkNat n)
  = Done MkNat

progress (MkBool b)
  = Done MkBool

progress (IfThenElseC c t f) with (progress c)
  progress (IfThenElseC (MkBool True) t y) | Done MkBool
    = Step ReduceCondCTrue

  progress (IfThenElseC (MkBool False) t y) | Done MkBool
    = Step ReduceCondCFalse

  progress (IfThenElseC (Seq l r) t y) | Done (Seq u v)
    = Step RewriteCondCTest

  progress (IfThenElseC c t y) | Step step
    = Step (SimplifyCondCTest step)

  progress (IfThenElseC c t y) | Halt reason
    = Halt reason

progress (NatOpArith op l r) with (progress l)
 progress (NatOpArith op (MkNat l) r) | (Done MkNat) with (progress r)

   progress (NatOpArith op (MkNat l) (MkNat r)) | (Done MkNat) | Done MkNat with (validArithOp op l r)
     progress (NatOpArith op (MkNat l) (MkNat r)) | (Done MkNat) | Done MkNat | (Yes prfWhy)
       = Step (ReduceNatArith prfWhy)
     progress (NatOpArith op (MkNat l) (MkNat r)) | (Done MkNat) | Done MkNat | (No msgWhyNot prfWhyNot)
      = Halt (ArithOpError msgWhyNot)

   progress (NatOpArith op (MkNat l) (Seq x y)) | (Done MkNat) | Done (Seq u v)
     = Step RewriteNatArithRight

   progress (NatOpArith op (MkNat l) r) | (Done MkNat) | Step step
     = Step (SimplifyNatArithRight step)

   progress (NatOpArith op (MkNat l) r) | (Done MkNat) | Halt reason
     = Halt reason

 progress (NatOpArith op (Seq x y) r) | Done (Seq u v)
   = Step RewriteNatArithLeft

 progress (NatOpArith op l r) | Step step
   = Step (SimplifyNatArithLeft step)

 progress (NatOpArith op l r) | Halt reason
   = Halt reason

-- ### Nat Comp
progress (NatOpCmp   op l r) with (progress l)
 progress (NatOpCmp op (MkNat l) r) | (Done MkNat) with (progress r)

   progress (NatOpCmp op (MkNat l) (MkNat r)) | (Done MkNat) | Done MkNat
     = Step ReduceNatCmp

   progress (NatOpCmp op (MkNat l) (Seq x y)) | (Done MkNat) | Done (Seq u v)
     = Step RewriteNatCmpRight

   progress (NatOpCmp op (MkNat l) r) | (Done MkNat) | Step step
     = Step (SimplifyNatCmpRight step)

   progress (NatOpCmp op (MkNat l) r) | (Done MkNat) | Halt reason
     = Halt reason

 progress (NatOpCmp op (Seq x y) r) | Done (Seq u v)
   = Step RewriteNatCmpLeft

 progress (NatOpCmp op l r) | Step step
   = Step (SimplifyNatCmpLeft step)

 progress (NatOpCmp op l r) | Halt reason
   = Halt reason

-- ### Bool Op
progress (BoolOpBin op l r) with (progress l)
 progress (BoolOpBin op (MkBool l) r) | (Done MkBool) with (progress r)

   progress (BoolOpBin op (MkBool l) (MkBool r)) | (Done MkBool) | Done MkBool
     = Step ReduceBoolOp

   progress (BoolOpBin op (MkBool l) (Seq x y)) | (Done MkBool) | Done (Seq u v)
     = Step RewriteBoolOpRight

   progress (BoolOpBin op (MkBool l) r) | (Done MkBool) | Step step
     = Step (SimplifyBoolOpRight step)

   progress (BoolOpBin op (MkBool l) r) | (Done MkBool) | Halt reason
     = Halt reason

 progress (BoolOpBin op (Seq x y) r) | Done (Seq u v)
   = Step RewriteBoolOpLeft

 progress (BoolOpBin op l r) | Step step
   = Step (SimplifyBoolOpLeft step)

 progress (BoolOpBin op l r) | Halt reason
   = Halt reason

-- ### Not
progress (BoolNot b) with (progress b)
  progress (BoolNot (MkBool f)) | (Done MkBool)
    = Step ReduceBoolNot

  progress (BoolNot (Seq l r)) | (Done (Seq x y))
    = Step RewriteBoolNot

  progress (BoolNot b) | (Step step)
    = Step (SimplifyBoolNot step)
  progress (BoolNot b) | (Halt reason)
    = Halt reason

progress (For cnt body) with (progress cnt)
  progress (For (MkNat n) body) | Done MkNat with (progress body)
    progress (For (MkNat 0) (FuncParam ty def body (IsValidTermDef IsNatTy y) (IsNat ChkNat))) | Done MkNat | (Done (FuncP (IsNat ChkNat)))
      = Step RewriteForZ
    progress (For (MkNat (S k)) (FuncParam ty def body (IsValidTermDef IsNatTy y) (IsNat ChkNat))) | Done MkNat | (Done (FuncP (IsNat ChkNat)))
      = Step RewriteForS

    progress (For (MkNat n) (Seq left right)) | Done MkNat | (Done (Seq x y))
      = Step RewriteForBody

    progress (For (MkNat n) body) | Done MkNat | (Step step)
      = Step (SimplifyForBody step)
    progress (For (MkNat n) body) | Done MkNat | (Halt reason)
      = Halt reason

  progress (For (Seq l r) body) | Done (Seq x y)
    = Step RewriteForCounter

  progress (For cnt body) | Step step
    = Step (SimplifyForCounter step)

  progress (For cnt body) | Halt reason
    = Halt reason

--progress (Var _) impossible

-- [ EOF ]
