module SystemV.Params.Evaluation.Reduction

import Toolkit.Data.Whole

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Terms.Renaming
import SystemV.Params.Terms.Substitution

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Predicates
import SystemV.Params.Evaluation.Values.Overridden

import SystemV.Params.Evaluation.Casting
import SystemV.Params.Evaluation.Slicing
import SystemV.Params.Evaluation.Sizing
import SystemV.Params.Evaluation.Indexing
import SystemV.Params.Evaluation.Comparing
import SystemV.Params.Evaluation.Arith

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

    -- ### Defaulting Functions
    SimplifyTyFuncDParam : Redux this that
                        -> Redux (TyFuncD this return prf)
                                 (TyFuncD that return prf)

    RewriteTyFuncDParam : Redux (TyFuncD (Seq left param) return prf)
                                (Seq left (TyFuncD param return prf))

    SimplifyTyFuncDReturn : {u : Universe}
                         -> {paramTYPE : TYPE u}
                         -> {returnTYPE : TYPE (IDX TYPE)}
                         -> {this, that : SystemV ctxt returnTYPE}
                         -> {param : SystemV ctxt paramTYPE}

                         -> {prf : Function.ValidType (IDX TYPE)
                                                      (FuncDefTy u paramTYPE returnTYPE)}

                         -> Redux this that
                         -> Redux (TyFuncD param this prf)
                                  (TyFuncD param that prf)

    RewriteTyFuncDReturn : Redux (TyFuncD param (Seq left return) prf)
                                 (Seq left (TyFuncD param return prf))

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

    -- ### Override

    SimplifyTyOverride : Redux this that
                      -> Redux (TyOverride this) (TyOverride that)


{-
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

-}
    -- ## Hardware

    -- ### Ports

    SimplifyMkPort : Redux this that
                  -> Redux (MkPort this dir) (MkPort that dir)

    -- ### Channels

    -- #### Channel Creation

    SimplifyMkChan : Redux this that
                  -> Redux (MkChan this) (MkChan that)


    -- ##### Projection

    -- ###### WriteTo
    SimplifyWriteTo : (chan : Redux this that)
                           -> Redux (WriteTo this) (WriteTo that)

    RewriteWriteTo : Redux (WriteTo (Seq left port))
                           (Seq left (WriteTo port))

    ReduceWriteTo : Redux (WriteTo (MkChan typeD)) (MkPort typeD OUT)

    -- ###### ReadFrom
    SimplifyReadFrom : (chan : Redux this that)
                            -> Redux (ReadFrom this) (ReadFrom that)

    RewriteReadFrom : Redux (ReadFrom (Seq left port))
                            (Seq left (ReadFrom port))

    ReduceReadFrom : Redux (ReadFrom (MkChan typeD)) (MkPort typeD IN)

    -- ##### Termintation

    -- ###### Driving
    SimplifyDrive : (chan : Redux this that)
                         -> Redux (Drive this) (Drive that)

    RewriteDrive : Redux (Drive (Seq left port))
                         (Seq left (Drive port))

    -- ###### Catching
    SimplifyCatch : (chan : Redux this that)
                         -> Redux (Catch this) (Catch that)

    RewriteCatch : Redux (Catch (Seq left port))
                         (Seq left (Catch port))

    -- #### Runtime Conditionals

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

    ReduceCastOverride : {prf      : ValidCast (PortTy tyA dirFrom) (PortTy tyTo dirTo)}
                      -> {tyFromTm : SystemV ctxt tyFrom}
                      -> (val      : Value tyFromTm)
                      -> (prfC     : ValidCast (PortTy tyFrom dirFrom) (PortTy tyTo dirTo))
                                  -> Redux (Cast (MkPort (TyOverride tyFromTm) dirFrom) prf)
                                           (cast prfC (MkPort tyFromTm dirFrom) (MkPort val dirFrom))

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

    ReduceSlice : {alpha : SystemV Nil (NatTy a)}
               -> {omega : SystemV Nil (NatTy o)}

               -> (valp  : Value port)
               -> (vala  : Value alpha)
               -> (valo  : Value omega)
               -> (vargs : Args port  valp
                                alpha vala
                                omega valo)
                        -> Redux (Slice port alpha omega prf)
                                 (slice port  valp
                                        alpha vala
                                        omega valo
                                        prf
                                        vargs)

    -- ### Indexing
    SimplifyIndexI : Redux this that
                  -> Redux (Index this port prf)
                           (Index that port prf)

    RewriteIndexI : Redux (Index (Seq left n) port prf)
                          (Seq left (Index n port prf))

    SimplifyIndexPort : {idx : SystemV ctxt (NatTy n)}
                     -> {this,that : SystemV ctxt (PortTy (VectorTyDesc s datatype) dir)}
                     -> Value idx
                     -> Redux this that
                     -> Redux (Index idx this prf)
                              (Index idx that prf)

    RewriteIndexPort : Redux (Index idx (Seq left port) prf)
                             (Seq left (Index idx port prf))


    ReduceIndex : (vali  : Value i)
               -> (valp  : Value port)
               -> (vargs : Indexing.Args i vali port valp)
               -> Redux (Index i port prf)
                        (index i vali port valp vargs)

    -- ### Size
    SimplifySize : Redux this that
                -> Redux (Size this)
                         (Size that)

    RewriteSize : Redux (Size (Seq left port))
                        (Seq left (Size port))

    ReduceSize : (value : Value port)
              -> (args  : Args port value)
                       -> Redux (Size port)
                                (sizeOf port value args)
{-
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

-}

    -- ## Booleans

    -- ### Negation
    SimplifyOpNot : Redux this that
                 -> Redux (OpNot this)
                          (OpNot that)

    RewriteOpNot : Redux (OpNot (Seq x y))
                         (Seq x (OpNot y))

    ReduceOpNotT : Redux (OpNot (B True))
                         (B False)
    ReduceOpNotF : Redux (OpNot (B False))
                         (B True)

    -- ### Binary
    SimplifyOpBoolL : Redux this that
                   -> Redux (OpBool op this r)
                            (OpBool op that r)

    RewriteOpBoolL : Redux (OpBool op (Seq x y) r)
                           (Seq x (OpBool op y r))

    SimplifyOpBoolR : {left : SystemV ctxt BoolTy}
                   -> Value  left
                   -> Redux  this that
                   -> Redux (OpBool op left this)
                            (OpBool op left that)

    RewriteOpBoolR : Redux (OpBool op left (Seq x y))
                           (Seq x (OpBool op left y))

    ReduceOpBool : Redux (OpBool op (B l) (B r))
                         (B (op l r))


    -- ### Cmp
    SimplifyOpCmpL : Redux this that
                  -> Redux (OpCmp op this r)
                           (OpCmp op that r)

    RewriteOpCmpL : Redux (OpCmp op (Seq x y) r)
                          (Seq x (OpCmp op y r))

    SimplifyOpCmpR :  {this,that : SystemV ctxt (NatTy r)}
                  -> {left : SystemV ctxt (NatTy l)}
                   -> Value  left
                   -> Redux  this that
                   -> Redux (OpCmp op left this)
                            (OpCmp op left that)

    RewriteOpCmpR : Redux (OpCmp op left (Seq x y))
                          (Seq x (OpCmp op left y))

    ReduceOpCmp : (valueL : Value left)
               -> (valueR : Value right)
               -> (vargs  : Comparing.Args left  valueL
                                 right valueR)
                        -> Redux (OpCmp op left right)
                                 (compare op left  valueL
                                             right valueR
                                             vargs)

{-

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
-}
-- --------------------------------------------------------------------- [ EOF ]
