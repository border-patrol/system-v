module SystemV.Params.Evaluation.Progress

import Toolkit.Decidable.Equality.Views

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms


import SystemV.Params.Terms.Renaming
import SystemV.Params.Terms.Substitution

import SystemV.Params.Evaluation.Error
import SystemV.Params.Evaluation.Values

import SystemV.Params.Evaluation.Casting
import SystemV.Params.Evaluation.Slicing

import SystemV.Params.Evaluation.Equality
import SystemV.Params.Evaluation.Check

import SystemV.Params.Evaluation.Reduction

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
        -> (reason : Params.Evaluation.Error)
                  -> Progress term

export
progress : (term : SystemV Nil type)
        -> Progress term

-- [ Types ]
progress (DATATYPE fc)
  = Done DATATYPE

progress (TyUnit fc)
  = Done TyUnit

progress (TyModule fc)
  = Done TyModule

progress (TyNat fc)
  = Done TyNat

progress (TyBool fc)
  = Done TyBool

progress (TyChan fc typeD) with (progress typeD)
  progress (TyChan fc typeD) | (Done value)
    = Done (TyChan value)
  progress (TyChan fc typeD) | (Step step)
    = Step (SimplifyTyChan step)
  progress (TyChan fc typeD) | Halt err
    = Halt err

progress (TyPort fc typeD dir) with (progress typeD)
  progress (TyPort fc typeD dir) | (Done value)
    = Done (TyPort value dir)
  progress (TyPort fc typeD dir) | (Step step)
    = Step (SimplifyTyPort step)
  progress (TyPort fc typeD dir) | (Halt err)
    = Halt err

progress (TyLogic fc)
  = Done TyLogic

progress (TyVect fc s typeE) with (progress s)
  progress (TyVect fc (MkNat fcn n) typeE) | (Done MkNat) with (progress typeE)
    progress (TyVect fc (MkNat fcn n) typeE) | (Done MkNat) | (Done value) with (isItSucc n)
      progress (TyVect fc (MkNat fcn (S n)) typeE) | (Done MkNat) | (Done value) | (Yes ItIsSucc)
        = Done (TyVect value ItIsSucc)

      progress (TyVect fc (MkNat fcn n) typeE) | (Done MkNat) | (Done value) | (No contra)
        = Halt (Err fc VectorCannotBeZero)

    progress (TyVect fc (MkNat fcn n) typeE) | (Done MkNat) | (Step step)
      = Step (SimplifyTyVectType step)
    progress (TyVect fc (MkNat fcn n) typeE) | (Done MkNat) | (Halt reason)
      = Halt reason

  progress (TyVect _ (Seq _ left right IsMod) typeE) | (Done (Seq x y)) impossible
  progress (TyVect _ (Seq _ left right IsUnit) typeE) | (Done (Seq x y)) impossible

  progress (TyVect fc s typeE) | (Step step)
    = Step (SimplifyTyVectSize step)
  progress (TyVect fc s typeE) | (Halt reason)
    = Halt reason

-- [ Terms ]

-- ### STLC


progress (Func fc x body prf vld) = Done Func

progress (App fc func param) with (progress func)
  progress (App fc (Func fcf ty body prf vld) param) | (Done Func) with (progress param)

    progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Done value) with (progress ty)
      progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Done value) | (Done tyV) with (check ty tyV param value prf vld)
        progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Done value) | (Done tyV) | Left err
          = case err of
             TypeMismatch a b => Halt (Err fc  (TypeMismatch a b))

        progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Done value) | (Done tyV) | (Right x)
          = Step (ReduceFunc tyV value x {body=body})

      progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Done value) | (Step step)
        = Step (SimplifyFuncAppType step)
      progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Done value) | (Halt reason)
        = Halt reason

    progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Step step)
      = Step (SimplifyFuncAppVar Func step)

    progress (App fc (Func fcf ty body prf vld) param) | (Done Func) | (Halt err)
      = Halt err

  progress (App _ (Seq _ left right IsMod) param) | (Done (Seq x y)) impossible
  progress (App _ (Seq _ left right IsUnit) param) | (Done (Seq x y)) impossible

  progress (App fc func param) | (Step step)
    = Step (SimplifyFuncAppFunc step)

  progress (App fc func param) | (Halt err)
    = Halt err

-- #### Paramterised Functions
progress (FuncParam fc x def body prf chk) = Done (FuncP chk)

-- #### App Override

progress (AppOver fc func var) with (progress func)
  progress (AppOver fc (FuncParam fcf ty def body prf chk) var) | (Done (FuncP chk)) with (progress var)
    progress (AppOver fc (FuncParam fcf ty def body prf chk) var) | (Done (FuncP chk)) | (Done value)
      = Step ReduceAppOver

    progress (AppOver fc (FuncParam fcf ty def body prf chk) var) | (Done (FuncP chk)) | (Step step)
      = Step (SimplifyAppOverVar (FuncP chk) step)

    progress (AppOver fc (FuncParam fcf ty def body prf chk) var) | (Done (FuncP chk)) | (Halt reason)
      = Halt reason

  progress (AppOver _ (Seq _ left right IsMod) var) | (Done (Seq x y)) impossible
  progress (AppOver _ (Seq _ left right IsUnit) var) | (Done (Seq x y)) impossible

  progress (AppOver fc func var) | (Step step)
    = Step (SimplifyAppOverFun step)

  progress (AppOver fc func var) | (Halt reason)
    = Halt reason

-- #### Application Default
progress (AppDef fc func) with (progress func)
  progress (AppDef fc (FuncParam fcf ty def body prf chk)) | Done (FuncP chk)
    = Step ReduceAppDef

  progress (AppDef _ (Seq _ l r IsUnit)) | Done (Seq u v) impossible
  progress (AppDef _ (Seq _ l r IsMod)) | Done (Seq u v) impossible

  progress (AppDef fc func) | Step step
    = Step (SimplifyAppDef step)

  progress (AppDef fc func) | Halt reason
    = Halt reason

-- ### Modules, Ports, & Unit

progress (MkUnit fc)
  = Done MkUnit

progress (EndModule fc)
  = Done EndModule

progress (MkPort fc typeD dir) with (progress typeD)
  progress (MkPort fc typeD dir) | (Done value)
    = Done (MkPort value dir)

  progress (MkPort fc typeD dir) | (Step step)
    = Step (SimplifyMkPort step)

  progress (MkPort fc typeD dir) | (Halt err)
    = Halt err

-- ### Channels

progress (MkChan fc typeD) with (progress typeD)
  progress (MkChan fc typeD) | (Done value)
    = Done (MkChan value)

  progress (MkChan fc typeD) | (Step step)
    = Step (SimplifyMkChan step)

  progress (MkChan fc typeD) | (Halt err)
    = Halt err

progress (WriteTo fc chan) with (progress chan)
  progress (WriteTo fc (MkChan fcc port)) | (Done (MkChan portVal))
    = Step ReduceWriteTo

  progress (WriteTo _ (Seq _ left right IsMod)) | (Done (Seq x y)) impossible
  progress (WriteTo _ (Seq _ left right IsUnit)) | (Done (Seq x y)) impossible

  progress (WriteTo fc chan) | (Step step)
   = Step (SimplifyWriteTo step)

  progress (WriteTo fc chan) | (Halt err)
    = Halt err

progress (ReadFrom fc chan) with (progress chan)
  progress (ReadFrom fc (MkChan fcf port)) | (Done (MkChan portVal))
    = Step ReduceReadFrom

  progress (ReadFrom _ (Seq _ left right IsMod)) | (Done (Seq x y)) impossible
  progress (ReadFrom _ (Seq _ left right IsUnit)) | (Done (Seq x y)) impossible

  progress (ReadFrom fc chan) | (Step step)
    = Step (SimplifyReadFrom step)

  progress (ReadFrom fc chan) | (Halt err)
    = Halt err

progress (Drive fc chan) with (progress chan)
  progress (Drive fc (MkPort fcp ty OUT)) | (Done (MkPort tyV OUT))
    = Done (Drive    (MkPort    tyV OUT))

  progress (Drive _ (Seq _ left right IsMod)) | (Done (Seq x y)) impossible
  progress (Drive _ (Seq _ left right IsUnit)) | (Done (Seq x y)) impossible

  progress (Drive fc chan) | (Step step)
    = Step (SimplifyDrive step)

  progress (Drive fc chan) | (Halt err)
    = Halt err

progress (Catch fc chan) with (progress chan)
  progress (Catch fc (MkPort fcp ty IN)) | (Done (MkPort tyV IN))
    = Done (Catch (MkPort tyV IN))

  progress (Catch _ (Seq _ left right IsUnit)) | (Done (Seq x y)) impossible
  progress (Catch _ (Seq _ left right IsMod)) | (Done (Seq x y)) impossible

  progress (Catch fc chan) | (Step step)
   = Step (SimplifyCatch step)

  progress (Catch fc chan) | (Halt err)
   = Halt err

-- ### Decisions & Connections
progress (IfThenElseR fc test whenIsZ whenNotZ) with (progress test)
  progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) with (progress whenIsZ)
    progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) with (progress whenNotZ)
      progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Done false)
        = Done (IfThenElseR    (MkPort     tyV IN) true false)

      progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Step step)
        = Step (SimplifyCondFalse step)

      progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Done true) | (Halt err)
        = Halt err

    progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Step step)
      = Step (SimplifyCondTrue step)

    progress (IfThenElseR fc (MkPort fcp ty IN) whenIsZ whenNotZ) | (Done (MkPort tyV IN)) | (Halt err)
      = Halt err

  progress (IfThenElseR _ (Seq _ left right IsMod) whenIsZ whenNotZ) | (Done (Seq x y)) impossible
  progress (IfThenElseR _ (Seq _ left right IsUnit) whenIsZ whenNotZ) | (Done (Seq x y)) impossible

  progress (IfThenElseR fc test whenIsZ whenNotZ) | (Step step)
    = Step (SimplifyCondTest step)

  progress (IfThenElseR fc test whenIsZ whenNotZ) | (Halt err)
    = Halt err

-- #### Connections
progress (Connect fc portL portR prf) with (progress portL)
  progress (Connect fc (MkPort fcpa tyL dirL) portR prf) | (Done (MkPort x dirL)) with (progress portR)
    progress (Connect fc (MkPort fcpa tyL dirL) (MkPort fcpb tyR dirR) prf) | (Done (MkPort x dirL)) | (Done (MkPort y dirR))
      = case decEq tyL x tyR y of
          No c => Halt (Err fc (TypeMismatch tyL tyR))
          Yes prf => Done (Connect (MkPort x dirL) (MkPort y dirR))

    progress (Connect _ (MkPort _ tyL dirL) (Seq _ left right IsMod) prf) | (Done (MkPort x dirL)) | (Done (Seq y z)) impossible
    progress (Connect _ (MkPort _ tyL dirL) (Seq _ left right IsUnit) prf) | (Done (MkPort x dirL)) | (Done (Seq y z)) impossible

    progress (Connect fc (MkPort fcpa tyL dirL) portR prf) | (Done (MkPort x dirL)) | (Step step)
      = Step (SimplifyConnectRight step)

    progress (Connect fc (MkPort fcpa tyL dirL) portR prf) | (Done (MkPort x dirL)) | (Halt err)
      = Halt err

  progress (Connect _ (Seq _ left right IsMod) portR prf) | (Done (Seq x y)) impossible
  progress (Connect _ (Seq _ left right IsUnit) portR prf) | (Done (Seq x y)) impossible

  progress (Connect fc portL portR prf) | (Step step)
    = Step (SimplifyConnectLeft step)

  progress (Connect fc portL portR prf) | (Halt err)
    = Halt err

-- ### Casting & Slicing
progress (Cast fc portA type dir prf) with (progress portA)
  progress (Cast fc (MkPort fcpa ty dirA) type dir prf) | (Done (MkPort x dirA)) with (progress type)
    progress (Cast fc (MkPort fcpa ty dirA) type dir prf) | (Done (MkPort x dirA)) | (Done value)
      = case checkCast prf (MkPort fcpa ty dirA) (MkPort x dirA) type value of
          Left err =>
             case err of
               TypeMismatch a b => Halt (Err fc (TypeMismatch a b))
          Right prfC => Step (ReduceCast (MkPort x dirA) value prfC)

    progress (Cast fc (MkPort fcpa ty dirA) type dir prf) | (Done (MkPort x dirA)) | (Step step)
      = Step (SimplifyCastType step)

    progress (Cast fc (MkPort fcpa ty dirA) type dir prf) | (Done (MkPort x dirA)) | (Halt reason)
      = Halt reason

  progress (Cast _ (Seq _ left right IsUnit) type dir prf) | (Done (Seq x y)) impossible
  progress (Cast _ (Seq _ left right IsMod) type dir prf) | (Done (Seq x y)) impossible

  progress (Cast fc portA type dir prf) | (Step step)
    = Step (SimplifyCastPort step)

  progress (Cast fc portA type dir prf) | (Halt err)
    = Halt err

-- #### Slicing

progress (Slice fc port alpha omega) with (progress port)
  progress (Slice fc (MkPort fcp tyP dir) alpha omega) | (Done (MkPort x dir)) with (progress alpha)
    progress (Slice fc (MkPort fcp tyP dir) (MkNat fca a) omega) | (Done (MkPort x dir)) | (Done MkNat) with (progress omega)
      progress (Slice fc (MkPort fcp tyP dir) (MkNat fca a) (MkNat fco o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) with (x)
        progress (Slice fc (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir) (MkNat fca a) (MkNat fco o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | (TyVect y z) with (validBound a o (W s z))
          progress (Slice fc (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir) (MkNat fca a) (MkNat fco o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | (TyVect y z) | (Yes prfWhy)
            = Step (ReduceSlice z prfWhy)

          progress (Slice fc (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir) (MkNat fca a) (MkNat fco o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | (TyVect y z) | (No msgWhyNot prfWhyNot)
            = Halt (InvalidBound msgWhyNot)

        progress (Slice fc (MkPort fcp (TyLogic fcl) dir) (MkNat fca a) (MkNat fco o)) | (Done (MkPort x dir)) | (Done MkNat) | (Done MkNat) | TyLogic
          = Halt (Err fc ExpectedVector)

      progress (Slice _ (MkPort _ tyP dir) (MkNat _ a) (Seq _ l r IsUnit)) | (Done (MkPort x dir)) | (Done MkNat) | (Done (Seq x' y)) impossible
      progress (Slice _ (MkPort _ tyP dir) (MkNat _ a) (Seq _ l r IsMod)) | (Done (MkPort x dir)) | (Done MkNat) | (Done (Seq x' y)) impossible

      progress (Slice fc (MkPort fcp tyP dir) (MkNat fca a) omega) | (Done (MkPort x dir)) | (Done MkNat) | (Step step)
        = Step (SimplifySliceOmega step)

      progress (Slice fc (MkPort fcp tyP dir) (MkNat fca a) omega) | (Done (MkPort x dir)) | (Done MkNat) | (Halt reason)
        = Halt reason

    progress (Slice _ (MkPort _ tyP dir) (Seq _ l r IsUnit) omega) | (Done (MkPort x dir)) | (Done (Seq x' y)) impossible
    progress (Slice _ (MkPort _ tyP dir) (Seq _ l r IsMod) omega) | (Done (MkPort x dir)) | (Done (Seq x' y)) impossible

    progress (Slice fc (MkPort fcp tyP dir) alpha omega) | (Done (MkPort x dir)) | (Step step)
      = Step (SimplifySliceAlpha step)
    progress (Slice fc (MkPort fcp tyP dir) alpha omega) | (Done (MkPort x dir)) | (Halt reason)
      = Halt reason

  progress (Slice _ (Seq _ left right IsMod) alpha omega) | (Done (Seq x y)) impossible
  progress (Slice _ (Seq _ left right IsUnit) alpha omega) | (Done (Seq x y)) impossible

  progress (Slice fc port alpha omega) | (Step step)
    = Step (SimplifySlicePort step)

  progress (Slice fc port alpha omega) | (Halt err)
    = Halt err

-- #### Indexing
progress (Index fc n port) with (progress port)
  progress (Index fc n (MkPort fcp ty dir)) | (Done (MkPort tyV dir)) with (progress n)
    progress (Index fc (MkNat fcn n) (MkPort fcp ty dir)) | (Done (MkPort tyV dir)) | (Done MkNat) with (tyV)
      progress (Index fc (MkNat fcn n) (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | (TyVect x y) with (isLTE (S n) s)
        progress (Index fc (MkNat fcn n) (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | (TyVect x y) | (Yes prf)
          = Step (ReduceIndex prf)
        progress (Index fc (MkNat fcn n) (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | (TyVect x y) | (No contra)
          = Halt (IndexOutOfBounds n (W s y))
      progress (Index fc (MkNat fcn n) (MkPort fcp (TyLogic fcl) dir)) | (Done (MkPort tyV dir)) | (Done MkNat) | TyLogic
        = Halt (Err fc ExpectedVector)

    progress (Index _ (Seq _ l r IsMod) (MkPort _ ty dir)) | (Done (MkPort tyV dir)) | (Done (Seq x y)) impossible
    progress (Index _ (Seq _ l r IsUnit) (MkPort _ ty dir)) | (Done (MkPort tyV dir)) | (Done (Seq x y)) impossible

    progress (Index fc n (MkPort fcp ty dir)) | (Done (MkPort tyV dir)) | (Step step)
      = Step (SimplifyIndexIdx step)
    progress (Index fc n (MkPort fcp ty dir)) | (Done (MkPort tyV dir)) | (Halt reason)
      = Halt reason

  progress (Index _ n (Seq _ left right IsUnit)) | (Done (Seq x y)) impossible
  progress (Index _ n (Seq _ left right IsMod)) | (Done (Seq x y)) impossible

  progress (Index fc n port) | (Step step)
    = Step (SimplifyIndexPort step)

  progress (Index fc n port) | (Halt err)
   = Halt err

-- #### Size

progress (Size fc port) with (progress port)
  progress (Size fc (MkPort fcp ty dir)) | (Done (MkPort tyV dir)) with (tyV)
    progress (Size fc (MkPort fcp (TyLogic fcl) dir)) | (Done (MkPort tyV dir)) | TyLogic
      = Halt (Err fc ExpectedVector)

    progress (Size fc (MkPort fcp (TyVect fcv (MkNat fcs s) ty) dir)) | (Done (MkPort tyV dir)) | (TyVect x y)
      = Step (ReduceSize)

  progress (Size fc (Seq _ left right IsUnit)) | (Done (Seq x y)) impossible
  progress (Size fc (Seq _ left right IsMod)) | (Done (Seq x y)) impossible

  progress (Size fc port) | (Step step)
    = Step (SimplifySizePort step)

  progress (Size fc port) | (Halt reason)
    = Halt reason

-- ### Gates

-- #### Not
progress (Not fc portO portI) with (progress portO)
  progress (Not fc (MkPort fcpa ty OUT) portI) | (Done (MkPort tyValO OUT)) with (progress portI)

    progress (Not fc (MkPort fcpa tyO OUT) (MkPort fcpb tyI IN)) | (Done (MkPort tyValO OUT)) | (Done (MkPort tyVa IN))
      = case decEq tyO tyValO tyI tyVa of
          Yes prf => Done (Not (MkPort tyValO OUT) (MkPort tyVa IN ))
          No contra => Halt (Err fc (TypeMismatch tyO tyI))

    progress (Not _ (MkPort _ tyO OUT) (Seq _ left right IsMod)) | (Done (MkPort tyValO OUT)) | (Done (Seq x y)) impossible
    progress (Not _ (MkPort _ tyO OUT) (Seq _ left right IsUnit)) | (Done (MkPort tyValO OUT)) | (Done (Seq x y)) impossible

    progress (Not fc (MkPort fcpa tyO OUT) portI) | (Done (MkPort tyValO OUT)) | (Step step)
      = Step (SimplifyNotIn step)

    progress (Not fc (MkPort fcpa tyO OUT) portI) | (Done (MkPort tyValO OUT)) | (Halt err)
      = Halt err

  progress (Not _ (Seq _ left right IsMod) portI) | (Done (Seq x y)) impossible
  progress (Not _ (Seq _ left right IsUnit) portI) | (Done (Seq x y)) impossible

  progress (Not fc portO portI) | (Step step)
    = Step (SimplifyNotOut step)

  progress (Not fc portO portI) | (Halt err)
    = Halt err

-- #### Binary

progress (Gate fc kind portO portIA portIB) with (progress portO)
  progress (Gate fc kind (MkPort fpca ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) with (progress portIA)
    progress (Gate fc kind (MkPort fpca ty OUT) (MkPort fcpb tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) with (progress portIB)
      progress (Gate fc kind (MkPort fcpa ty OUT) (MkPort fcpb tyIA IN) (MkPort fcpc tyIB IN)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (MkPort tyVIB IN))
        = case decEq ty tyV tyIA tyVIA of
            No c => Halt (Err fc (TypeMismatch ty tyIA))
            Yes prfAB =>
              case decEq ty tyV tyIB tyVIB of
                No c => Halt (Err fc (TypeMismatch ty tyIB))
                Yes prfBC => Done (Gate (MkPort tyV OUT) (MkPort tyVIA IN) (MkPort tyVIB IN))

      progress (Gate _ kind (MkPort _ ty OUT) (MkPort _ tyIA IN) (Seq _ left right IsMod)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (Seq x y)) impossible
      progress (Gate _ kind (MkPort _ ty OUT) (MkPort _ tyIA IN) (Seq _ left right IsUnit)) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Done (Seq x y)) impossible

      progress (Gate fc kind (MkPort fcpa ty OUT) (MkPort fcpb tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Step step)
        = Step (SimplifyBinInB step)

      progress (Gate fc kind (MkPort fcpa ty OUT) (MkPort fcpb tyIA IN) portIB) | (Done (MkPort tyV OUT)) | (Done (MkPort tyVIA IN)) | (Halt err)
        = Halt err

    progress (Gate _ kind (MkPort _ ty OUT) (Seq _ left right IsMod) portIB) | (Done (MkPort tyV OUT)) | (Done (Seq x y)) impossible
    progress (Gate _ kind (MkPort _ ty OUT) (Seq _ left right IsUnit) portIB) | (Done (MkPort tyV OUT)) | (Done (Seq x y)) impossible

    progress (Gate fc kind (MkPort fcpa ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) | (Step step)
      = Step (SimplifyBinInA step)

    progress (Gate fc kind (MkPort fcpa ty OUT) portIA portIB) | (Done (MkPort tyV OUT)) | (Halt err)
      = Halt err

  progress (Gate _ kind (Seq _ left right IsMod) portIA portIB) | (Done (Seq x y)) impossible
  progress (Gate _ kind (Seq _ left right IsUnit) portIA portIB) | (Done (Seq x y)) impossible

  progress (Gate fc kind portO portIA portIB) | (Step step)
    = Step (SimplifyBinOut step)

  progress (Gate fc kind portO portIA portIB) | (Halt err)
    = Halt err

-- ### Binders
progress (Let fc value body prf) with (progress value)
  progress (Let fc value body prf) | (Done val)
    = Step (ReduceLetBody val)

  progress (Let fc value body prf) | (Step step)
    = Step (SimplifyLetValue step)

  progress (Let fc value body prf) | (Halt err)
    = Halt err

-- ### Sequencing
progress (Seq fc left right prf) with (progress left)

  progress (Seq fc (Seq fci l r IsUnit) right prf) | (Done (Seq x y))
    = Step RewriteSeq

  progress (Seq fc left right prf) | (Done value) with (progress right)
    progress (Seq fc left right prf) | (Done l) | (Done r)
      = Done (Seq l r)

    progress (Seq fc left right prf) | (Done l) | (Step step)
      = Step (SimplifySeqRight l step)

    progress (Seq fc left right prf) | (Done l) | (Halt reason)
      = Halt reason

  progress (Seq fc left right prf) | (Step step)
    = Step (SimplifySeqLeft step)

  progress (Seq fc left right prf) | (Halt reason)
    = Halt reason

-- ### Nats & Bools

progress (MkNat fc n)
  = Done MkNat

progress (MkBool fc b)
  = Done MkBool

progress (IfThenElseC fc c t f) with (progress c)
  progress (IfThenElseC fc (MkBool fcb True) t y) | Done MkBool
    = Step ReduceCondCTrue

  progress (IfThenElseC fc (MkBool fcb False) t y) | Done MkBool
    = Step ReduceCondCFalse

  progress (IfThenElseC _ (Seq _ l r IsUnit) t y) | Done (Seq u v) impossible
  progress (IfThenElseC _ (Seq _ l r IsMod) t y) | Done (Seq u v) impossible

  progress (IfThenElseC fc c t y) | Step step
    = Step (SimplifyCondCTest step)

  progress (IfThenElseC fc c t y) | Halt reason
    = Halt reason

progress (NatOpArith fc op l r) with (progress l)
 progress (NatOpArith fc op (MkNat fcl l) r) | (Done MkNat) with (progress r)

   progress (NatOpArith fc op (MkNat fcl l) (MkNat fcr r)) | (Done MkNat) | Done MkNat with (validArithOp op l r)
     progress (NatOpArith fc op (MkNat fcl l) (MkNat fcr r)) | (Done MkNat) | Done MkNat | (Yes prfWhy)
       = Step (ReduceNatArith prfWhy)
     progress (NatOpArith fc op (MkNat fcl l) (MkNat fcr r)) | (Done MkNat) | Done MkNat | (No msgWhyNot prfWhyNot)
      = Halt (ArithOpError msgWhyNot)

   progress (NatOpArith _ op (MkNat _ l) (Seq _ x y IsUnit)) | (Done MkNat) | Done (Seq u v) impossible
   progress (NatOpArith _ op (MkNat _ l) (Seq _ x y IsMod)) | (Done MkNat) | Done (Seq u v) impossible

   progress (NatOpArith fc op (MkNat fcl l) r) | (Done MkNat) | Step step
     = Step (SimplifyNatArithRight step)

   progress (NatOpArith fc op (MkNat fcl l) r) | (Done MkNat) | Halt reason
     = Halt reason

 progress (NatOpArith _ op (Seq _ x y IsMod) r) | Done (Seq u v) impossible
 progress (NatOpArith _ op (Seq _ x y IsUnit) r) | Done (Seq u v) impossible

 progress (NatOpArith fc op l r) | Step step
   = Step (SimplifyNatArithLeft step)

 progress (NatOpArith fc op l r) | Halt reason
   = Halt reason

-- ### Nat Comp
progress (NatOpCmp fc op l r) with (progress l)
 progress (NatOpCmp fc op (MkNat fcl l) r) | (Done MkNat) with (progress r)

   progress (NatOpCmp fc op (MkNat fcl l) (MkNat fcr r)) | (Done MkNat) | Done MkNat
     = Step ReduceNatCmp

   progress (NatOpCmp fc op (MkNat _ l) (Seq _ x y IsUnit)) | (Done MkNat) | Done (Seq u v) impossible
   progress (NatOpCmp fc op (MkNat _ l) (Seq _ x y IsMod)) | (Done MkNat) | Done (Seq u v) impossible


   progress (NatOpCmp fc op (MkNat fcl l) r) | (Done MkNat) | Step step
     = Step (SimplifyNatCmpRight step)

   progress (NatOpCmp fc op (MkNat fcl l) r) | (Done MkNat) | Halt reason
     = Halt reason

 progress (NatOpCmp fc op (Seq _ x y IsUnit) r) | Done (Seq u v) impossible
 progress (NatOpCmp fc op (Seq _ x y IsMod) r) | Done (Seq u v) impossible

 progress (NatOpCmp fc op l r) | Step step
   = Step (SimplifyNatCmpLeft step)

 progress (NatOpCmp fc op l r) | Halt reason
   = Halt reason

-- ### Bool Op
progress (BoolOpBin fc op l r) with (progress l)
 progress (BoolOpBin fc op (MkBool fcl l) r) | (Done MkBool) with (progress r)

   progress (BoolOpBin fc op (MkBool fcl l) (MkBool fcr r)) | (Done MkBool) | Done MkBool
     = Step ReduceBoolOp

   progress (BoolOpBin _ op (MkBool _ l) (Seq _ x y IsUnit)) | (Done MkBool) | Done (Seq u v) impossible
   progress (BoolOpBin _ op (MkBool _ l) (Seq _ x y IsMod)) | (Done MkBool) | Done (Seq u v) impossible


   progress (BoolOpBin fc op (MkBool fcl l) r) | (Done MkBool) | Step step
     = Step (SimplifyBoolOpRight step)

   progress (BoolOpBin fc op (MkBool fcl l) r) | (Done MkBool) | Halt reason
     = Halt reason

 progress (BoolOpBin _ op (Seq _ x y IsUnit) r) | Done (Seq u v) impossible
 progress (BoolOpBin _ op (Seq _ x y IsMod) r) | Done (Seq u v) impossible

 progress (BoolOpBin fc op l r) | Step step
   = Step (SimplifyBoolOpLeft step)

 progress (BoolOpBin fc op l r) | Halt reason
   = Halt reason

-- ### Not
progress (BoolNot fc b) with (progress b)
  progress (BoolNot fc (MkBool fcb f)) | (Done MkBool)
    = Step ReduceBoolNot

  progress (BoolNot fc (Seq _ l r IsUnit)) | (Done (Seq x y)) impossible
  progress (BoolNot fc (Seq _ l r IsMod)) | (Done (Seq x y)) impossible

  progress (BoolNot fc b) | (Step step)
    = Step (SimplifyBoolNot step)
  progress (BoolNot fc b) | (Halt reason)
    = Halt reason

progress (For fc cnt body) with (progress cnt)
  progress (For fc (MkNat fcn 0) body) | Done MkNat
    = Step RewriteForZ

  progress (For fc (MkNat fcn (S k)) body) | Done MkNat
    = Step RewriteForS

  progress (For _ (Seq _ l r IsUnit) body) | Done (Seq x y) impossible
  progress (For _ (Seq _ l r IsMod) body) | Done (Seq x y) impossible

  progress (For fc cnt body) | Step step
    = Step (SimplifyForCounter step)

  progress (For fc cnt body) | Halt reason
    = Halt reason

--progress (Var _) impossible

-- [ EOF ]
