module SystemV.Annotated.Evaluation.Reduction

import SystemV.Common.Utilities
import SystemV.Annotated.Types
import SystemV.Annotated.Terms

import SystemV.Annotated.Terms.Renaming
import SystemV.Annotated.Terms.Substitution

import SystemV.Annotated.Values

import SystemV.Annotated.Evaluation.Casting
import SystemV.Annotated.Evaluation.Slicing
import SystemV.Annotated.Evaluation.Indexing

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
                  -> Redux (TyChan this sense intent) (TyChan that sense intent)

    -- ### Ports

    SimplifyTyPort : Redux this that
                  -> Redux (TyPort this dir sense intent) (TyPort that dir sense intent)

    -- ### Vectors

    SimplifyTyVect : Redux this that
                  -> Redux (TyVect s this) (TyVect s that)

    -- ## Function Application

    SimplifyFuncAppFunc : Redux this that
                       -> Redux (App this a)
                                (App that a)

    RewriteFuncAppFunc : Redux (App (Seq left func) param)
                               (Seq left (App func param))

    SimplifyFuncAppVar : {func : SystemV ctxt (FuncTy param return)}

                      -> Value func
                      -> Redux this that
                      -> Redux (App func this)
                               (App func that)


    ReduceFunc : {param, return : TYPE (IDX TERM)}
              -> {body          : SystemV (ctxt += param) return}
              -> {a             : SystemV  ctxt    param}
              -> {type          : SystemV  ctxt    paramTyDesc}
              -> {prfTyCheck    : TyCheck paramTyDesc param}
              -> {prfValid      : Function.ValidTerm (IDX TERM) (FuncTy param return)}

              -> Value a
              -> Redux (App (Func type body prfTyCheck prfValid) a)
                            (subst a body)

    -- ## Hardware

    -- ### Ports

    SimplifyMkPort : Redux this that
                  -> Redux (MkPort this dir sense intent) (MkPort that dir sense intent)

    -- ### Channels

    -- ### Channel Creation

    SimplifyMkChan : Redux this that
                  -> Redux (MkChan this sense intent) (MkChan that sense intent)

    -- #### Projection

    -- ##### WriteTo
    SimplifyWriteTo : (chan : Redux this that)
                           -> Redux (WriteTo this) (WriteTo that)

    RewriteWriteTo : Redux (WriteTo (Seq left port))
                           (Seq left (WriteTo port))

    ReduceWriteTo : Redux (WriteTo (MkChan typeD sense intent)) (MkPort typeD OUT sense intent)

    -- ##### ReadFrom
    SimplifyReadFrom : (chan : Redux this that)
                            -> Redux (ReadFrom this) (ReadFrom that)

    RewriteReadFrom : Redux (ReadFrom (Seq left port))
                            (Seq left (ReadFrom port))

    ReduceReadFrom : Redux (ReadFrom (MkChan typeD sense intent)) (MkPort typeD IN sense intent)

    -- #### Signalling

    -- ##### Driving
    SimplifyDrive : (chan : Redux this that)
                         -> Redux (Drive s i this) (Drive s i that)

    RewriteDrive : Redux (Drive s i (Seq left port))
                         (Seq left (Drive s i port))

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


    ReduceSlice : (val : Value port)
                      -> Redux (Slice port (a) (o) prf)
                               (slice a o prf port val)

    -- ### Indexing
    SimplifyIndexPort : Redux this that
                     -> Redux (Index (n) this prf)
                              (Index (n) that prf)

    RewriteIndexPort : Redux (Index (n) (Seq left port) prf)
                             (Seq left (Index (n) port prf))

    ReduceIndex : (val : Value port)
                      -> Redux (Index (n) port prf)
                               (index n port prf val)

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

-- --------------------------------------------------------------------- [ EOF ]
