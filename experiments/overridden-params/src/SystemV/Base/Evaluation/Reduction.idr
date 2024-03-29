module SystemV.Base.Evaluation.Reduction

import SystemV.Common.Utilities
import SystemV.Base.Types
import SystemV.Base.Terms

import SystemV.Base.Terms.Renaming
import SystemV.Base.Terms.Substitution

import SystemV.Base.Evaluation.Values
import SystemV.Base.Evaluation.Casting
import SystemV.Base.Evaluation.Slicing
import SystemV.Base.Evaluation.Sizing
import SystemV.Base.Evaluation.Indexing

%default total

public export
data Redux : (this : SystemV ctxt type)
          -> (that : SystemV ctxt type)
          -> Type
  where


    -- ## Types

    -- ### Functions

    SimplifyTyFuncParam : Redux this that
                       -> Redux (TyFunc this return prf)
                                (TyFunc that return prf)

    RewriteTyFuncParam : Redux (TyFunc (Seq left param) return prf)
                               (Seq left (TyFunc param return prf))

    SimplifyTyFuncReturn : Redux this that
                        -> Redux (TyFunc param this prf)
                                 (TyFunc param that prf)

    RewriteTyFuncReturn : Redux (TyFunc param (Seq left return) prf)
                                (Seq left (TyFunc param return prf))

    -- ### Channels

    SimplifyTyChan : Redux this that
                  -> Redux (TyChan this) (TyChan that)

    -- ### Ports

    SimplifyTyPort : Redux this that
                  -> Redux (TyPort this dir) (TyPort that dir)

    -- ### TypeDefs

    SimplifyTyTypeDef : Redux this that
                     -> Redux (TyTypeDef this) (TyTypeDef that)


    -- ### Vectors

    SimplifyTyVect : Redux this that
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


    ReduceFunc : {param, return : TYPE (IDX TERM)}
              -> {body          : SystemV (ctxt += param) return}
              -> {var           : SystemV  ctxt    param}
              -> {type          : SystemV  ctxt    paramTyDesc}
              -> {prfTyCheck    : TyCheck paramTyDesc param}
              -> {prfValid      : Function.ValidTerm (IDX TERM) (FuncTy param return)}

              -> Value var
              -> Redux (App (Func type body prfTyCheck prfValid) var)
                            (subst var body)

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

    SimplifyCast : Redux this that
                -> Redux (Cast this prf)
                         (Cast that prf)

    RewriteCast : Redux (Cast (Seq left port) prf)
                        (Seq left (Cast port prf))

    ReduceCast : (val : Value port)
                     -> Redux (Cast port prf)
                              (cast prf port val)

    -- ### Slicing

    SimplifySlicePort : Redux this that
                     -> Redux (Slice this alpha omega prf)
                              (Slice that alpha omega prf)

    RewriteSlicePort : Redux (Slice (Seq left port) alpha omega prf)
                             (Seq left (Slice port alpha omega prf))

    SimplifySliceA : Redux this that
                  -> Redux (Slice port this omega prf)
                           (Slice port that omega prf)

    RewriteSliceA : Redux (Slice port (Seq left alpha) omega prf)
                          (Seq left (Slice port alpha omega prf))

    SimplifySliceO : Redux this that
                  -> Redux (Slice port alpha this prf)
                           (Slice port alpha that prf)

    RewriteSliceO : Redux (Slice port alpha (Seq left omega) prf)
                          (Seq left (Slice port alpha omega prf))

    ReduceSlice : (val : Value port)
                      -> Redux (Slice port (MkNat a) (MkNat o) prf)
                               (slice a o prf port val)

    -- ### Indexing
    SimplifyIndexI : Redux this that
                  -> Redux (Index this port prf)
                           (Index that port prf)

    RewriteIndexI : Redux (Index (Seq left n) port prf)
                          (Seq left (Index n port prf))

    SimplifyIndexPort : Redux this that
                     -> Redux (Index (MkNat n) this prf)
                              (Index (MkNat n) that prf)

    RewriteIndexPort : Redux (Index (MkNat n) (Seq left port) prf)
                             (Seq left (Index (MkNat n) port prf))

    ReduceIndex : (val : Value port)
                      -> Redux (Index (MkNat n) port prf)
                               (index n port prf val)

    -- ### Size
    SimplifySize : Redux this that
                -> Redux (Size this)
                         (Size that)

    RewriteSize : Redux (Size (Seq left port))
                        (Seq left (Size port))

    ReduceSize : (v : Value port)
              -> Redux (Size port)
                       (size port v)

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
{-    -- ### For

    SimplifyForCounter : Redux this that
                      -> Redux (For this body)
                               (For that body)

    SimplifyForBody : Redux this that
                   -> Redux (For (MkNat n) this)
                            (For (MkNat n) that)

    RewriteForCounter : Redux (For (Seq left right) body)
                              (Seq left (For right body))


    RewriteForZ : Redux (For (MkNat Z) body)
                        (App body (MkNat Z))

    RewriteForSFunc : (body' : SystemV ctxt (FuncTy (NatTy m) UnitTy))

                            -> Redux (For (MkNat (S m)) (Func type body prf))
                                     (Seq (For (MkNat m) body')
                                          (App (Func type body prf) (MkNat (S m))))

    RewriteForSSeqSeq : Redux (For (MkNat (S m)) (Seq left (Seq right func)))
                              (Seq left
                                   (For (MkNat (S m)) (Seq right func)))

    RewriteForSSeqFunc : Redux (For (MkNat (S m)) (Seq left (Func type body prf)))
                               (Seq left
                                    (For (MkNat (S m)) (Func type body prf)))
-}

-- --------------------------------------------------------------------- [ EOF ]
