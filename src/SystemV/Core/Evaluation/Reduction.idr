module SystemV.Core.Evaluation.Reduction

import SystemV.Common.Utilities
import SystemV.Core.Types
import SystemV.Core.Terms

import SystemV.Core.Terms.Renaming
import SystemV.Core.Terms.Substitution

import SystemV.Core.Values

import SystemV.Core.Evaluation.Casting
import SystemV.Core.Evaluation.Slicing
import SystemV.Core.Evaluation.Indexing

%default total

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

    SimplifyTyVect : Redux this that
                  -> Redux (TyVect s this) (TyVect s that)

    -- ## Function Application

    SimplifyFuncAppFunc : Redux this that
                       -> Redux (App this var)
                                (App that var)


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

    ReduceWriteTo : Redux (WriteTo (MkChan typeD)) (MkPort typeD OUT)

    -- ##### ReadFrom
    SimplifyReadFrom : (chan : Redux this that)
                            -> Redux (ReadFrom this) (ReadFrom that)

    ReduceReadFrom : Redux (ReadFrom (MkChan typeD)) (MkPort typeD IN)

    -- #### Signalling

    -- ##### Driving
    SimplifyDrive : (chan : Redux this that)
                         -> Redux (Drive this) (Drive that)


    -- ##### Catching
    SimplifyCatch : (chan : Redux this that)
                         -> Redux (Catch this) (Catch that)


    -- ### Conditionals

    SimplifyCondTest : Redux this that
                    -> Redux (IfThenElseR this t f)
                             (IfThenElseR that t f)


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

    SimplifyConnectRight : Redux this that
                        -> Redux (Connect portL this prf)
                                 (Connect portL that prf)

    -- ### Casting

    SimplifyCast : Redux this that
                -> Redux (Cast this prf)
                         (Cast that prf)


    ReduceCast : (val : Value port)
                     -> Redux (Cast port prf)
                              (cast prf port val)

    -- ### Slicing

    SimplifySlicePort : Redux this that
                     -> Redux (Slice this alpha omega prf)
                              (Slice that alpha omega prf)

    ReduceSlice : (val : Value port)
                      -> Redux (Slice port (a) (o) prf)
                               (slice a o prf port val)

    -- ### Indexing
    SimplifyIndexPort : Redux this that
                     -> Redux (Index (n) this prf)
                              (Index (n) that prf)


    ReduceIndex : (val : Value port)
                      -> Redux (Index (n) port prf)
                               (index n port prf val)

    -- ### Gates

    -- #### Not

    SimplifyNotOut : Redux this that
                  -> Redux (Not this input)
                           (Not that input)

    SimplifyNotIn : Redux this that
                 -> Redux (Not out this)
                          (Not out that)

    -- #### Binary

    SimplifyBinOut : Redux this that
                  -> Redux (Gate k this inA inB)
                           (Gate k that inA inB)


    SimplifyBinInA : Redux this that
                  -> Redux (Gate k out this inB)
                           (Gate k out that inB)


    SimplifyBinInB : Redux this that
                  -> Redux (Gate k out inA this)
                           (Gate k out inA that)

    -- ## Let-Binders

    SimplifyLetValue : {this, that : SystemV  ctxt    typeV}
                    -> {body       : SystemV (ctxt += typeV) typeB}

                    -> (value      : Redux this that)
                                  -> Redux (Let this body prf)
                                           (Let that body prf)

    ReduceLetBody : {value : SystemV  ctxt    typeV}
                 -> {body  : SystemV (ctxt += typeV) typeB}

                          -> Value value
                          -> Redux (Let value body prf)
                                   (subst value body)
    -- ## Sequencing

    -- ### Seq

    SimplifySeqLeft : {this, that : SystemV ctxt UnitTy}
                   -> {right      : SystemV ctxt type}

                   -> Redux this that
                   -> Redux (Seq this right prf)
                            (Seq that right prf)

    SimplifySeqRight : {left : SystemV ctxt UnitTy}
                    -> {this, that : SystemV ctxt type}

                    -> Value left
                    -> Redux this that
                    -> Redux (Seq left this prf)
                             (Seq left that prf)

    RewriteSeq : {a,b : SystemV ctxt UnitTy}
              -> {c   : SystemV ctxt type}

                     -> Redux (Seq (Seq a b IsUnit) c pB)
                              (Seq a (Seq b c pB) pB)

-- --------------------------------------------------------------------- [ EOF ]
