module SystemV.Param.Evaluation.Reduction

import SystemV.Common.Utilities

import SystemV.Param.Types
import SystemV.Param.Terms

import SystemV.Param.Terms.Renaming
import SystemV.Param.Terms.Substitution

import SystemV.Param.Evaluation.Values
import SystemV.Param.Evaluation.Slicing
import SystemV.Param.Evaluation.Casting

import SystemV.Param.Evaluation.Check

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
                  -> Redux (TyChan this) (TyChan that)

    -- ### Ports

    SimplifyTyPort : Redux this that
                  -> Redux (TyPort this dir) (TyPort that dir)

    -- ### Vectors
    SimplifyTyVectSize : Redux this that
                      -> Redux (TyVect this type)
                               (TyVect that type)


    SimplifyTyVectType : Redux this that
                      -> Redux (TyVect s this) (TyVect s that)

    -- ## Function Application

    SimplifyFuncAppFunc : Redux this that
                       -> Redux (App this var)
                                (App that var)

    RewriteFuncAppFunc : Redux (App (Seq left func) param)
                               (Seq left (App func param))

    SimplifyFuncAppVar : {func : SystemV ctxt (FuncTy param return)}

                      -> Value func
                      -> Redux this that
                      -> Redux (App func this)
                               (App func that)

    SimplifyFuncAppType : {param, return : TYPE (IDX TERM)}
                       -> {body          : SystemV (ctxt += param) return}
                       -> {var           : SystemV  ctxt    param}
                       -> {this,that     : SystemV  ctxt    paramTyDesc}
                       -> {prfTyCheck    : TyCheck paramTyDesc param}
                       -> {prfValid      : Function.ValidTerm (IDX TERM) (FuncTy param return)}
                       -> Redux this that
                       -> Redux (App (Func this body prfTyCheck prfValid) var)
                                (App (Func that body prfTyCheck prfValid) var)

    ReduceFunc : {param, return : TYPE (IDX TERM)}
              -> {body          : SystemV (ctxt += param) return}
              -> {var           : SystemV  ctxt    param}
              -> {type          : SystemV  ctxt    paramTyDesc}
              -> {prfTyCheck    : TyCheck paramTyDesc param}
              -> {prfValid      : Function.ValidTerm (IDX TERM) (FuncTy param return)}
              -> (typeV         : Value type)
              -> (varV          : Value var)
              -> Check type typeV var varV
              -> Redux (App (Func type body prfTyCheck prfValid) var)
                            (subst var body)

    -- ### Param Function Application

    -- #### AppOver
    SimplifyAppOverFun : {this,that : SystemV ctxt (FuncParamTy u term b)}
                                   -> Redux this that
                                   -> Redux (AppOver this v)
                                            (AppOver that v)

    RewriteAppOverFun : Redux (AppOver (Seq left func) var)
                              (Seq left (AppOver func var))

    SimplifyAppOverVar : {func       : SystemV ctxt (FuncParamTy u term b)}
                      -> {this, that : SystemV ctxt term}
                                    -> Value func
                                    -> Redux this that
                                    -> Redux (AppOver func this)
                                             (AppOver func that)

    ReduceAppOver : Redux (AppOver (FuncParam type def body chk prf) var)
                          (subst var body)

    -- #### AppDef
    SimplifyAppDef : {this,that : SystemV ctxt (FuncParamTy u term b)}
                               -> Redux this that
                               -> Redux (AppDef this)
                                        (AppDef that)

    RewriteAppDef : Redux (AppDef (Seq left func))
                          (Seq left (AppDef func))

    ReduceAppDef : Redux (AppDef (FuncParam type def body chk prf))
                         (subst def body)
    -- ## Hardware

    -- ### Ports

    SimplifyMkPort : Redux this that
                  -> Redux (MkPort this dir) (MkPort that dir)

    -- ### Channels

    -- ### Channel Creation

    SimplifyMkChan : Redux this that
                  -> Redux (MkChan this) (MkChan that)

    -- #### Projection

    -- ##### WriteTo
    SimplifyWriteTo : (chan : Redux this that)
                           -> Redux (WriteTo this) (WriteTo that)

    RewriteWriteTo : Redux (WriteTo (Seq left port))
                           (Seq left (WriteTo port))

    ReduceWriteTo : Redux (WriteTo (MkChan typeD)) (MkPort typeD OUT)

    -- ##### ReadFrom
    SimplifyReadFrom : (chan : Redux this that)
                            -> Redux (ReadFrom this) (ReadFrom that)

    RewriteReadFrom : Redux (ReadFrom (Seq left port))
                            (Seq left (ReadFrom port))

    ReduceReadFrom : Redux (ReadFrom (MkChan typeD)) (MkPort typeD IN)

    -- #### Signalling

    -- ##### Driving
    SimplifyDrive : (chan : Redux this that)
                         -> Redux (Drive this) (Drive that)

    RewriteDrive : Redux (Drive (Seq left port))
                         (Seq left (Drive port))

    -- ##### Catching
    SimplifyCatch : (chan : Redux this that)
                         -> Redux (Catch this) (Catch that)

    RewriteCatch : Redux (Catch (Seq left port))
                         (Seq left (Catch port))

    -- ### Conditionals

    SimplifyCondTest : Redux this that
                    -> Redux (IfThenElseR this t f)
                             (IfThenElseR that t f)

    RewriteCondTest : Redux (IfThenElseR (Seq left test) t f)
                            (Seq left (IfThenElseR test t f))

    SimplifyCondTrue : Redux this that
                    -> Redux (IfThenElseR test this f)
                             (IfThenElseR test that f)

    SimplifyCondFalse : Redux this that
                     -> Redux (IfThenElseR test t this)
                              (IfThenElseR test t that)

    -- ### Connections
    SimplifyConnectLeft : Redux this that
                       -> Redux (Connect this portR prf)
                                (Connect that portR prf)

    RewriteConnectLeft : Redux (Connect (Seq left portL) portR prf)
                               (Seq left (Connect portL portR prf))

    SimplifyConnectRight : Redux this that
                        -> Redux (Connect portL this prf)
                                 (Connect portL that prf)

    RewriteConnectRight : Redux (Connect portL (Seq left portR) prf)
                                (Seq left (Connect portL portR prf))

    -- ### Casting

    SimplifyCastPort : Redux this that
                    -> Redux (Cast this type dir prf)
                             (Cast that type dir prf)

    RewriteCastPort : Redux (Cast (Seq left port) type dir prf)
                            (Seq left (Cast port type dir prf))

    SimplifyCastType : Redux this that
                    -> Redux (Cast port this dir prf)
                             (Cast port that dir prf)

    ReduceCast : {port : SystemV Nil (PortTy dirA)}
              -> {type : SystemV Nil DATATERM}
              -> {prf  : ValidCast (PortTy dirA)
                                   (PortTy dirB)}
              -> (val  : Value port)
              -> (valt : Value type)
              -> (prfC : CheckCast prf port val type valt)
                     -> Redux (Cast port type dirB prf)
                              (cast prf port val type valt prfC)

    -- ### Slicing

    SimplifySlicePort : Redux this that
                     -> Redux (Slice this alpha omega)
                              (Slice that alpha omega)

    RewriteSlicePort : Redux (Slice (Seq left port) alpha omega)
                             (Seq left (Slice port alpha omega))

    SimplifySliceAlpha : Redux this that
                      -> Redux (Slice port this omega)
                               (Slice port that omega)

    RewriteSliceAlpha : Redux (Slice port (Seq left alpha) omega)
                              (Seq left (Slice port alpha omega))

    SimplifySliceOmega : Redux this that
                      -> Redux (Slice port alpha this)
                               (Slice port alpha that)

    RewriteSliceOmega : Redux (Slice port alpha (Seq left omega))
                              (Seq left (Slice port alpha omega))

    ReduceSlice : {type : SystemV ctxt DATATERM}
               -> (prfWhole : IsSucc s)
               -> (prf      : ValidBound a o (W s prfWhole))
                           -> Redux (Slice (MkPort (TyVect (MkNat s) type) dir) (MkNat a) (MkNat o))
                                    (slice a o s prfWhole prf type dir)

    -- ### Indexing
    SimplifyIndexIdx : Redux this that
                    -> Redux (Index this port)
                             (Index that port)

    RewriteIndexIdx : Redux (Index (Seq left idx) port)
                            (Seq left (Index idx port))

    SimplifyIndexPort : Redux this that
                     -> Redux (Index (n) this)
                              (Index (n) that)

    RewriteIndexPort : Redux (Index (n) (Seq left port))
                             (Seq left (Index (n) port))

    ReduceIndex : {type : SystemV ctxt DATATERM}
               -> (prf  : LTE (S i) s)
                       -> Redux (Index (MkNat i) (MkPort (TyVect (MkNat s) type) dir))
                                (MkPort type dir)

    -- ### Size
    SimplifySizePort : Redux this that
                    -> Redux (Size this) (Size that)

    RewriteSize : Redux (Size (Seq left port))
                        (Seq left (Size port))


    ReduceSize : Redux (Size (MkPort (TyVect (MkNat w) ty) dir))
                       (MkNat w)
    -- ### Gates

    -- #### Not

    SimplifyNotOut : Redux this that
                  -> Redux (Not this input)
                           (Not that input)

    RewriteNotOutSeq : Redux (Not (Seq left right) input)
                             (Seq left (Not right input))

    SimplifyNotIn : Redux this that
                 -> Redux (Not out this)
                          (Not out that)

    RewriteNotInSeq : Redux (Not out (Seq left input))
                            (Seq left (Not out input))

    -- #### Binary

    SimplifyBinOut : Redux this that
                  -> Redux (Gate k this inA inB)
                           (Gate k that inA inB)

    RewriteBinOut : Redux (Gate k (Seq left out) inA inB)
                          (Seq left (Gate k out inA inB))

    SimplifyBinInA : Redux this that
                  -> Redux (Gate k out this inB)
                           (Gate k out that inB)

    RewriteBinInA : Redux (Gate k out (Seq left inA) inB)
                          (Seq left (Gate k out inA inB))

    SimplifyBinInB : Redux this that
                  -> Redux (Gate k out inA this)
                           (Gate k out inA that)

    RewriteBinInB : Redux (Gate k out inA (Seq left inB))
                          (Seq left (Gate k out inA inB))

    -- ## Let-Binders

    SimplifyLetValue : {this, that : SystemV  ctxt    typeV}
                    -> {body       : SystemV (ctxt += typeV) typeB}

                    -> (value      : Redux this that)
                                  -> Redux (Let this body)
                                           (Let that body)

    ReduceLetBody : {value : SystemV  ctxt    typeV}
                 -> {body  : SystemV (ctxt += typeV) typeB}

                          -> Value value
                          -> Redux (Let value body)
                                   (subst value body)
    -- ## Sequencing

    -- ### Seq

    SimplifySeqLeft : {this, that : SystemV ctxt UnitTy}
                   -> {right      : SystemV ctxt type}

                   -> Redux this that
                   -> Redux (Seq this right)
                            (Seq that right)

    SimplifySeqRight : {left : SystemV ctxt UnitTy}
                    -> {this, that : SystemV ctxt type}

                    -> Value left
                    -> Redux this that
                    -> Redux (Seq left this)
                             (Seq left that)

    RewriteSeq : {a,b : SystemV ctxt UnitTy}
              -> {c   : SystemV ctxt type}

                     -> Redux (Seq (Seq a b) c)
                              (Seq a (Seq b c))

    -- Operations
    SimplifyNatArithLeft : Redux this that
                        -> Redux (NatOpArith op this right)
                                 (NatOpArith op that right)

    RewriteNatArithLeft : Redux (NatOpArith op (Seq left l) right)
                                (Seq left (NatOpArith op l right))

    SimplifyNatArithRight : Redux this that
                         -> Redux (NatOpArith op left this)
                                  (NatOpArith op left that)

    RewriteNatArithRight : Redux (NatOpArith op left (Seq l r))
                                 (Seq l (NatOpArith op left r))

    ReduceNatArith : {op  : ArithOp}
                  -> {l,r : Nat}
                  -> (prf : Valid op l r)
                         -> Redux (the (SystemV Nil NatTy) (NatOpArith op (MkNat l) (MkNat r))) -- UGLY
                                  (MkNat (apply op l r prf))

    -- ### Nat Cmp
    SimplifyNatCmpLeft : Redux this that
                      -> Redux (NatOpCmp op this right)
                               (NatOpCmp op that right)

    RewriteNatCmpLeft : Redux (NatOpCmp op (Seq left r) right)
                              (Seq left (NatOpCmp op r right))

    SimplifyNatCmpRight : Redux this that
                       -> Redux (NatOpCmp op left this)
                                (NatOpCmp op left that)

    RewriteNatCmpRight : Redux (NatOpCmp op left (Seq l right))
                               (Seq l (NatOpCmp op left right))

    ReduceNatCmp : Redux (NatOpCmp op (MkNat l) (MkNat r))
                         (MkBool (apply op l r))

    -- ### Bool Op
    SimplifyBoolOpLeft : Redux this that
                      -> Redux (BoolOpBin op this right)
                               (BoolOpBin op that right)

    RewriteBoolOpLeft : Redux (BoolOpBin op (Seq left r) right)
                              (Seq left (BoolOpBin op r right))

    SimplifyBoolOpRight : Redux this that
                       -> Redux (BoolOpBin op left this)
                                (BoolOpBin op left that)

    RewriteBoolOpRight : Redux (BoolOpBin op left (Seq l right))
                               (Seq l (BoolOpBin op left right))

    ReduceBoolOp : Redux (BoolOpBin op (MkBool l) (MkBool r))
                         (MkBool (Boolean.apply op l r))

    -- ### Not

    SimplifyBoolNot : Redux this that
                   -> Redux (BoolNot this) (BoolNot that)

    RewriteBoolNot : Redux (BoolNot (Seq left b))
                           (Seq left (BoolNot b))

    ReduceBoolNot : Redux (BoolNot (MkBool b))
                          (MkBool (not b))

    -- ### Cond

    SimplifyCondCTest : Redux this that
                     -> Redux (IfThenElseC this t f)
                              (IfThenElseC that t f)

    RewriteCondCTest : Redux (IfThenElseC (Seq left test) t f)
                             (Seq left (IfThenElseC test t f))

    ReduceCondCTrue : Redux (IfThenElseC (MkBool True) t f)
                            t

    ReduceCondCFalse : Redux (IfThenElseC (MkBool False) t f)
                             f


    -- ### For

    SimplifyForCounter : Redux this that
                      -> Redux (For this body)
                               (For that body)

    SimplifyForBody : Redux this that
                   -> Redux (For cnt this)
                            (For cnt that)

    RewriteForCounter : Redux (For (Seq left right) body)
                              (Seq left (For right body))

    RewriteForBody : Redux (For cnt (Seq left func))
                           (Seq left (For cnt func))

    RewriteForZ : Redux (For (MkNat Z) (FuncParam ty def b p c))
                        (subst (MkNat Z) b)

    RewriteForS : Redux (For (MkNat (S m)) (FuncParam ty def b p c))
                        (Seq (For (MkNat m) (FuncParam ty def b p c))
                             (subst (MkNat (S m)) b))
-- --------------------------------------------------------------------- [ EOF ]
