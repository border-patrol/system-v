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

    SimplifyDriveChan : (chan : Redux this that)
                             -> Redux (Drive this val prf) (Drive that val prf)

    SimplifyDriveVal : {type      : MTy (DATA TYPE)}
                    -> {chan      : SystemV ctxt (ChanVal type)}
                    -> {this, that : SystemV ctxt typeVal}
                    -> {prf       : TyCheckData type typeVal}
                    -> (chanValue : Value chan)
                    -> (prfRedux  : Redux this that)
                                 -> Redux (Drive chan this prf)
                                          (Drive chan that prf)

    SimplifyCatch : (chan : Redux this that)
                         -> Redux (Catch this) (Catch that)

    -- Booleans
    SimplifyIsOnParam : (prf : Redux this that)
                            -> Redux (IsOnParam this) (IsOnParam that)

    SimplifyIsOnPort : (prf : Redux this that)
                           -> Redux (IsOnPort this) (IsOnPort that)

    SimplifyIfThenElseCond : (prf : Redux this that)
                                 -> Redux (IfThenElse this true false)
                                          (IfThenElse that true false)

    SimplifyIfThenElseTrue : (condValue : Value cond)
                          -> (prf       : Redux this that)
                                       -> Redux (IfThenElse cond this false)
                                                (IfThenElse cond that false)

    SimplifyIfThenElseFalse : (condValue : Value cond)
                           -> (condTrue  : Value true)
                           -> (prf       : Redux this that)
                                        -> Redux (IfThenElse cond true this)
                                                 (IfThenElse cond true that)

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


    -- Params
    SimplifyTyParam : (type : Redux this that)
                          -> Redux (TyParam this) (TyParam that)

    SimplifyMkParam : (type : Redux this that)
                          -> Redux (MkParam this) (MkParam that)

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
