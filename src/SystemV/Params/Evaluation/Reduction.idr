module SystemV.Params.Evaluation.Reduction

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Terms.Renaming
import SystemV.Params.Terms.Substitution

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Slicing
import SystemV.Params.Evaluation.Casting

import SystemV.Params.Evaluation.Check

%default total

-- @TODO Nat Arith Ops check div by zero


public export
data Redux : (this : SystemV ctxt type)
          -> (that : SystemV ctxt type)
          -> Type
  where


    -- ## Types

    -- ### Channels

    SimplifyTyChan : Redux this that
                  -> Redux (TyChan fc this) (TyChan fc that)

    -- ### Ports

    SimplifyTyPort : Redux this that
                  -> Redux (TyPort fc this dir) (TyPort fc that dir)

    -- ### Vectors
    SimplifyTyVectSize : Redux this that
                      -> Redux (TyVect fc this type)
                               (TyVect fc that type)


    SimplifyTyVectType : Redux this that
                      -> Redux (TyVect fc s this) (TyVect fc s that)

    -- ## Function Application

    SimplifyFuncAppFunc : Redux this that
                       -> Redux (App fc this var)
                                (App fc that var)

    SimplifyFuncAppVar : {func : SystemV ctxt (FuncTy param return)}

                      -> Value func
                      -> Redux this that
                      -> Redux (App fc func this)
                               (App fc func that)

    SimplifyFuncAppType : {param, return : TYPE (IDX TERM)}
                       -> {body          : SystemV (ctxt += param) return}
                       -> {var           : SystemV  ctxt    param}
                       -> {this,that     : SystemV  ctxt    paramTyDesc}
                       -> {prfTyCheck    : TyCheck paramTyDesc param}
                       -> {prfValid      : Function.ValidTerm (IDX TERM) (FuncTy param return)}
                       -> Redux this that
                       -> Redux (App fcA (Func fc this body prfTyCheck prfValid) var)
                                (App fcA (Func fc that body prfTyCheck prfValid) var)

    ReduceFunc : {param, return : TYPE (IDX TERM)}
              -> {body          : SystemV (ctxt += param) return}
              -> {var           : SystemV  ctxt    param}
              -> {type          : SystemV  ctxt    paramTyDesc}
              -> {prfTyCheck    : TyCheck paramTyDesc param}
              -> {prfValid      : Function.ValidTerm (IDX TERM) (FuncTy param return)}
              -> (typeV         : Value type)
              -> (varV          : Value var)
              -> Check type typeV var varV
              -> Redux (App fcA (Func fc type body prfTyCheck prfValid) var)
                               (subst var body)

    -- ### Param Function Application

    -- #### AppOver
    SimplifyAppOverFun : {this,that : SystemV ctxt (FuncParamTy u term b)}
                                   -> Redux this that
                                   -> Redux (AppOver fc this v)
                                            (AppOver fc that v)

    SimplifyAppOverVar : {func       : SystemV ctxt (FuncParamTy u term b)}
                      -> {this, that : SystemV ctxt term}
                                    -> Value func
                                    -> Redux this that
                                    -> Redux (AppOver fc func this)
                                             (AppOver fc func that)

    ReduceAppOver : Redux (AppOver fcA (FuncParam fc type def body chk prf) var)
                          (subst var body)

    -- #### AppDef
    SimplifyAppDef : {this,that : SystemV ctxt (FuncParamTy u term b)}
                               -> Redux this that
                               -> Redux (AppDef fc this)
                                        (AppDef fc that)

    ReduceAppDef : Redux (AppDef fca (FuncParam fc type def body chk prf))
                         (subst def body)
    -- ## Hardware

    -- ### Ports

    SimplifyMkPort : Redux this that
                  -> Redux (MkPort fc this dir) (MkPort fc that dir)

    -- ### Channels

    -- ### Channel Creation

    SimplifyMkChan : Redux this that
                  -> Redux (MkChan fc this) (MkChan fc that)

    -- #### Projection

    -- ##### WriteTo
    SimplifyWriteTo : (chan : Redux this that)
                           -> Redux (WriteTo fc this) (WriteTo fc that)

    ReduceWriteTo : Redux (WriteTo fc (MkChan fcc typeD)) (MkPort fcc typeD OUT)

    -- ##### ReadFrom
    SimplifyReadFrom : (chan : Redux this that)
                            -> Redux (ReadFrom fc this) (ReadFrom fc that)

    ReduceReadFrom : Redux (ReadFrom fc (MkChan fcc typeD)) (MkPort fcc typeD IN)

    -- #### Signalling

    -- ##### Driving
    SimplifyDrive : (chan : Redux this that)
                         -> Redux (Drive fc this) (Drive fc that)

    -- ##### Catching
    SimplifyCatch : (chan : Redux this that)
                         -> Redux (Catch fc this) (Catch fc that)

    -- ### Conditionals

    SimplifyCondTest : Redux this that
                    -> Redux (IfThenElseR fc this t f)
                             (IfThenElseR fc that t f)

    SimplifyCondTrue : Redux this that
                    -> Redux (IfThenElseR fc test this f)
                             (IfThenElseR fc test that f)

    SimplifyCondFalse : Redux this that
                     -> Redux (IfThenElseR fc test t this)
                              (IfThenElseR fc test t that)

    -- ### Connections
    SimplifyConnectLeft : Redux this that
                       -> Redux (Connect fc this portR prf)
                                (Connect fc that portR prf)

    SimplifyConnectRight : Redux this that
                        -> Redux (Connect fc portL this prf)
                                 (Connect fc portL that prf)

    -- ### Casting

    SimplifyCastPort : Redux this that
                    -> Redux (Cast fc this type dir prf)
                             (Cast fc that type dir prf)

    SimplifyCastType : Redux this that
                    -> Redux (Cast fc port this dir prf)
                             (Cast fc port that dir prf)

    ReduceCast : {port : SystemV Nil (PortTy dirA)}
              -> {type : SystemV Nil DATATERM}
              -> {prf  : ValidCast (PortTy dirA)
                                   (PortTy dirB)}
              -> (val  : Value port)
              -> (valt : Value type)
              -> (prfC : CheckCast prf port val type valt)
                     -> Redux (Cast fc port type dirB prf)
                              (cast prf port val type valt prfC)

    -- ### Slicing

    SimplifySlicePort : Redux this that
                     -> Redux (Slice fc this alpha omega)
                              (Slice fc that alpha omega)

    SimplifySliceAlpha : Redux this that
                      -> Redux (Slice fc port this omega)
                               (Slice fc port that omega)

    SimplifySliceOmega : Redux this that
                      -> Redux (Slice fc port alpha this)
                               (Slice fc port alpha that)

    ReduceSlice : {type : SystemV ctxt DATATERM}
               -> (prfWhole : IsSucc s)
               -> (prf      : ValidBound a o (W s prfWhole))
                           -> Redux (Slice fc (MkPort fcp (TyVect fcv (MkNat fcs s) type) dir) (MkNat fca a) (MkNat fco o))
                                    (slice fc a o s prfWhole prf type dir)

    -- ### Indexing
    SimplifyIndexIdx : Redux this that
                    -> Redux (Index fc this port)
                             (Index fc that port)

    SimplifyIndexPort : Redux this that
                     -> Redux (Index fc (n) this)
                              (Index fc (n) that)

    ReduceIndex : {type : SystemV ctxt DATATERM}
               -> (prf  : LTE (S i) s)
                       -> Redux (Index fc (MkNat fci i) (MkPort fcp (TyVect fcv (MkNat fcs s) type) dir))
                                (MkPort fc type dir)

    -- ### Size
    SimplifySizePort : Redux this that
                    -> Redux (Size fc this) (Size fc that)

    ReduceSize : Redux (Size fc (MkPort fcp (TyVect fcv (MkNat fcn w) ty) dir))
                       (MkNat fc w)
    -- ### Gates

    -- #### Not

    SimplifyNotOut : Redux this that
                  -> Redux (Not fc this input)
                           (Not fc that input)

    SimplifyNotIn : Redux this that
                 -> Redux (Not fc out this)
                          (Not fc out that)

    -- #### Binary

    SimplifyBinOut : Redux this that
                  -> Redux (Gate fc k this inA inB)
                           (Gate fc k that inA inB)

    SimplifyBinInA : Redux this that
                  -> Redux (Gate fc k out this inB)
                           (Gate fc k out that inB)

    SimplifyBinInB : Redux this that
                  -> Redux (Gate fc k out inA this)
                           (Gate fc k out inA that)

    -- ## Let-Binders

    SimplifyLetValue : {this, that : SystemV  ctxt    typeV}
                    -> {body       : SystemV (ctxt += typeV) typeB}

                    -> (value      : Redux this that)
                                  -> Redux (Let fc this body prf)
                                           (Let fc that body prf)

    ReduceLetBody : {value : SystemV  ctxt    typeV}
                 -> {body  : SystemV (ctxt += typeV) typeB}

                          -> Value value
                          -> Redux (Let fc value body prf)
                                   (subst value body)
    -- ## Sequencing

    -- ### Seq
    SimplifySeqLeft : {this, that : SystemV ctxt UnitTy}
                   -> {right      : SystemV ctxt type}

                   -> Redux this that
                   -> Redux (Seq fc this right prf)
                            (Seq fc that right prf)

    SimplifySeqRight : {left : SystemV ctxt UnitTy}
                    -> {this, that : SystemV ctxt type}

                    -> Value left
                    -> Redux this that
                    -> Redux (Seq fc left this prf)
                             (Seq fc left that prf)

    RewriteSeq : {a,b : SystemV ctxt UnitTy}
              -> {c   : SystemV ctxt type}

                     -> Redux (Seq fcO (Seq fcI a b IsUnit) c pB)
                              (Seq fcO a (Seq fcI b c pB) pB)

    -- Operations
    SimplifyNatArithLeft : Redux this that
                        -> Redux (NatOpArith fc op this right)
                                 (NatOpArith fc op that right)

    SimplifyNatArithRight : Redux this that
                         -> Redux (NatOpArith fc op left this)
                                  (NatOpArith fc op left that)

    ReduceNatArith : {op  : ArithOp}
                  -> {l,r : Nat}
                  -> (prf : Valid op l r)
                         -> Redux (the (SystemV Nil NatTy) (NatOpArith fc op (MkNat fcL l) (MkNat fcR r))) -- UGLY
                                  (MkNat fc (apply op l r prf))

    -- ### Nat Cmp
    SimplifyNatCmpLeft : Redux this that
                      -> Redux (NatOpCmp fc op this right)
                               (NatOpCmp fc op that right)

    SimplifyNatCmpRight : Redux this that
                       -> Redux (NatOpCmp fc op left this)
                                (NatOpCmp fc op left that)

    ReduceNatCmp : Redux (NatOpCmp fc op (MkNat fcL l) (MkNat fcR r))
                         (MkBool fc (apply op l r))

    -- ### Bool Op
    SimplifyBoolOpLeft : Redux this that
                      -> Redux (BoolOpBin fc op this right)
                               (BoolOpBin fc op that right)

    SimplifyBoolOpRight : Redux this that
                       -> Redux (BoolOpBin fc op left this)
                                (BoolOpBin fc op left that)

    ReduceBoolOp : Redux (BoolOpBin fc op (MkBool fcl l) (MkBool fcr r))
                         (MkBool fc (Boolean.apply op l r))

    -- ### Not

    SimplifyBoolNot : Redux this that
                   -> Redux (BoolNot fc this) (BoolNot fc that)

    ReduceBoolNot : Redux (BoolNot fc (MkBool fcI b))
                          (MkBool fc (not b))

    -- ### Cond

    SimplifyCondCTest : Redux this that
                     -> Redux (IfThenElseC fc this t f)
                              (IfThenElseC fc that t f)

    ReduceCondCTrue : Redux (IfThenElseC fc (MkBool fcb True) t f)
                            t

    ReduceCondCFalse : Redux (IfThenElseC fc (MkBool fcb False) t f)
                             f


    -- ### For

    SimplifyForCounter : Redux this that
                      -> Redux (For fc this body)
                               (For fc that body)


    RewriteForZ : Redux (For fcf (MkNat fcz Z) body)
                        (subst (MkNat fcz Z) body)

    RewriteForS : Redux (For fcf (MkNat fcm (S m)) body)
                        (Seq fcf (For fcf (MkNat fcm m) body)
                             (subst (MkNat fcm (S m)) body)
                             IsUnit)
-- --------------------------------------------------------------------- [ EOF ]
