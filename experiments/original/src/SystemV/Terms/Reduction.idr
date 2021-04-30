module SystemV.Terms.Reduction

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms
import SystemV.Values

import SystemV.Terms.Renaming
import SystemV.Terms.Substitution
import SystemV.Terms.Casting

%default total

public export
data Redux : (this : SystemV ctxt type)
          -> (that : SystemV ctxt type)
          -> Type
  where
    -- Functions reduce
    SimplifyFuncAppFunc : (func : Redux this that)
                               -> Redux (App this var)
                                        (App that var)

    SimplifyFuncAppVar : {this, that : SystemV ctxt type}
                      -> {func       : SystemV ctxt (FuncTy type return)}
                      -> (value      : Value func)
                      -> (var        : Redux this that)
                                    -> Redux (App func this)
                                             (App func that)

    ReduceFunc : (prf : Value var)
                     -> Redux (App (Func type body prfTyCheck) var)
                              (subst var body)

    -- Simplify Function Types
    SimplifyTyFuncParam : (param : Redux this that)
                                -> Redux (TyFunc this body)
                                         (TyFunc that body)

    SimplifyTyFuncBody : {this, that : SystemV ctxt type}
                      -> {param      : SystemV ctxt paramTy}
                      -> (value      : Value param)
                      -> (body       : Redux this that)
                                    -> Redux (TyFunc param this)
                                             (TyFunc param that)


    -- Matching Vects
    SimplifyTyVect : (prf : Redux this that)
                         -> Redux (TyVect s this) (TyVect s that)

    -- Matching newtypes
    SimplifyTypeDefType : (desc : Redux this that)
                               -> Redux (TypeDefType this) (TypeDefType that)

    SimplifyTypeDefCTorType : {this, that : SystemV ctxt (TypeDefTy typeM)}
                           -> {value      : SystemV ctxt type}
                           -> (theType    : Redux this that)
                                         -> Redux (TypeDefCTor this value prf)
                                                  (TypeDefCTor that value prf)

    SimplifyTypeDefCTorValue : {this, that : SystemV ctxt typeV}
                            -> {theType : SystemV ctxt (TypeDefTy typeD)}
                            -> (typeV   : Value theType)
                            -> (value   : Redux this that)
                                       -> Redux (TypeDefCTor theType this prf)
                                                (TypeDefCTor theType that prf)

    SimplifyTypeDef : {this, that : SystemV ctxt (TypeDefTy typeV)}
                   -> {body : SystemV (ctxt += (TypeDefTy typeV)) typeB}
                   -> (desc : Redux this that)
                           -> Redux (TypeDef this body)
                                    (TypeDef that body)

    ReduceTypeDef : {typeD : MTy (DATA TYPE)}
                 -> {typeB : MTy level}
                 -> {desc : SystemV ctxt (TypeDefTy typeD)}
                 -> {body : SystemV (ctxt += (TypeDefTy typeD)) typeB}
                 -> (value : Value desc)
                          -> Redux (TypeDef desc body)
                                   (subst   desc body)

    -- Ports
    SimplifyTyPort : (type : Redux this that)
                          -> Redux (TyPort this dir) (TyPort that dir)

    SimplifyMkPort : (type : Redux this that)
                          -> Redux (MkPort this dir) (MkPort that dir)

    -- Chans
    SimplifyTyChan : (type : Redux this that)
                          -> Redux (TyChan this) (TyChan that)

    SimplifyMkChan : (type : Redux this that)
                          -> Redux (MkChan this) (MkChan that)

    SimplifyWriteTo : (type : Redux this that)
                           -> Redux (WriteTo this) (WriteTo that)

    ReduceWriteTo : Value typeD
                 -> Redux (WriteTo (MkChan typeD)) (MkPort typeD OUT)

    SimplifyReadFrom : (type : Redux this that)
                            -> Redux (ReadFrom this) (ReadFrom that)

    ReduceReadFrom : Value typeD
                  -> Redux (ReadFrom (MkChan typeD)) (MkPort typeD IN)

    SimplifyDrive : (chan : Redux this that)
                         -> Redux (Drive this) (Drive that)

    SimplifyCatch : (chan : Redux this that)
                         -> Redux (Catch this) (Catch that)

    -- Booleans
    SimplifyIfThenElseRCond : (prf : Redux this that)
                                  -> Redux (IfThenElseR this true false)
                                           (IfThenElseR that true false)

    SimplifyIfThenElseRTrue : (condValue : Value cond)
                           -> (prf       : Redux this that)
                                        -> Redux (IfThenElseR cond this false)
                                                 (IfThenElseR cond that false)

    SimplifyIfThenElseRFalse : (condValue : Value cond)
                            -> (condTrue  : Value true)
                            -> (prf       : Redux this that)
                                         -> Redux (IfThenElseR cond true this)
                                                  (IfThenElseR cond true that)

    -- Connections

    SimplifyConnectLeft : {this,that : SystemV ctxt (PortVal type dirL)}
                       -> {portR     : SystemV ctxt (PortVal type dirR)}
                       -> (prf       : Redux this that)
                                    -> Redux (Connect this portR prf')
                                             (Connect that portR prf')

    SimplifyConnectRight : {portL : SystemV ctxt (PortVal type dirL)}
                        -> {this, that : SystemV ctxt (PortVal type dirR)}
                        -> (prf  : Value portL)
                        -> (port : Redux this that)
                                -> Redux (Connect portL this prf')
                                         (Connect portL that prf')

    SimplifyCast : {tyA,tyB    : MTy (DATA TYPE)}
                -> {dirA,dirB  : Direction}
                -> {this, that : SystemV ctxt (PortVal tyA dirA)}
                -> {prf        : ValidCast (PortVal tyA dirA)
                                           (PortVal tyB dirB)}
                              -> Redux this that
                              -> Redux (Cast this prf) (Cast that prf)

    ReduceCast : {tyA,tyB   : MTy (DATA TYPE)}
              -> {dirA,dirB : Direction}
              -> {from      : SystemV ctxt tyA}
              -> (value     : Value (MkPort from dirA))
              -> (prfValidC : ValidCast (PortVal tyA dirA) (PortVal tyB dirB))
                           -> Redux (Cast (MkPort from dirA) prfValidC)
                                    (cast prfValidC (MkPort from dirA) value)


    SimplifySlice : Redux this that
                 -> Redux (Slice this a o prf) (Slice that a o prf)

    ReduceSlice : {typeV : SystemV ctxt type}
               -> (value : Value (MkPort (TyVect sout typeV) dir))
               -> (prf   : CanSlice (DATA TYPE) (VectorTyDesc s type) a o (VectorTyDesc sout type))
                        -> Redux (Slice (MkPort (TyVect s typeV) dir) a o prf)
                                 (MkPort (TyVect sout typeV) dir)

    -- Params
    SimplifyParamOpBoolLeft : Redux this that
                           -> Redux (ParamOpBool op this right)
                                    (ParamOpBool op that right)

    SimplifyParamOpBoolRight : Value left
                            -> Redux this that
                            -> Redux (ParamOpBool op left this)
                                     (ParamOpBool op left that)

    ReduceParamOpBool : Redux (ParamOpBool op (MkParam left) (MkParam right))
                              (B (op left right))


    SimplifyParamOpNot : (prf : Redux this that)
                             -> Redux (ParamOpNot this)
                                      (ParamOpNot that)

    ReduceParamOpNot : Redux (ParamOpNot (B b))
                             (B (not b))

    SimplifyIfThenElseCCond : (prf : Redux this that)
                                  -> Redux (IfThenElseC this true false)
                                           (IfThenElseC that true false)

    ReduceIfThenElseCTrue : Redux (IfThenElseC (B True) true false)
                                  true

    ReduceIfThenElseCFalse : Redux (IfThenElseC (B False) true false)
                                   false

    -- Gates
    SimplifyNotOutput : Redux this that
                     -> Redux (Not this i) (Not that i)

    SimplifyNotInput : {o : SystemV ctxt (PortVal type OUT)}
                    -> Value o
                    -> Redux this that
                    -> Redux (Not o this) (Not o that)

    SimplifyGateOutput : Redux this that
                      -> Redux (Gate type this ia ib)
                               (Gate type that ia ib)

    SimplifyGateInputA : {out : SystemV ctxt (PortVal type OUT)}
                      -> Value out
                      -> Redux this that
                      -> Redux (Gate kind out this ib)
                               (Gate kind out that ib)

    SimplifyGateInputB : {out : SystemV ctxt (PortVal type OUT)}
                      -> {ia  : SystemV ctxt (PortVal type IN)}
                      -> Value out
                      -> Value ia
                      -> Redux this that
                      -> Redux (Gate kind out ia this)
                               (Gate kind out ia that)


    -- Let binding
    SimplifyLetValue : {this, that : SystemV ctxt typeV}
                    -> {body : SystemV (ctxt += typeV) typeB}
                    -> (value   : Redux this that)
                               -> Redux (Let this body)
                                        (Let that body)

    ReduceLetBody : {value    : SystemV  ctxt typeV}
                 -> {body     : SystemV (ctxt += typeV) typeB}
                 -> (valueVal : Value value)
                             -> Redux (Let value body)
                                      (subst value body)

-- --------------------------------------------------------------------- [ EOF ]
