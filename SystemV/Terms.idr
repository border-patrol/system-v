||| Terms in SystemV.
|||
module SystemV.Terms

import SystemV.Utilities
import SystemV.Types

%default total

public export
data SystemV : Context lvls -> MTy level -> Type where
  -- STLC
  Var : Elem Universe MTy type ctxt -> SystemV ctxt type

  Func : {  paramTyDesc     : MTy (IDX TYPE)}
      -> {  paramTy, bodyTy : MTy (IDX VALUE)}
      -> (  type : SystemV  ctxt    paramTyDesc)
      -> (  body : SystemV (ctxt +=             paramTy) bodyTy)
      -> (  prf  : TyCheck          paramTyDesc paramTy)
                -> SystemV  ctxt        (FuncTy paramTy  bodyTy)

  App : {paramTy, bodyTy : MTy (IDX VALUE)}
     -> (func  : SystemV ctxt (FuncTy paramTy  bodyTy))
     -> (value : SystemV ctxt         paramTy)
              -> SystemV ctxt                   bodyTy

  TyFunc : {paramMTy, returnMTy : MTy (IDX TYPE)}
        -> (paramTy  : SystemV ctxt paramMTy)
        -> (returnTy : SystemV ctxt returnMTy)
                    -> SystemV ctxt (FuncTy paramMTy returnMTy)

  -- Unityty
  TyUnit : SystemV ctxt UnitTy
  MkUnit : SystemV ctxt UnitVal

  -- Logic Type Constructors
  TyLogic : SystemV ctxt LogicTyDesc

  -- Booleans
  TyBool : SystemV ctxt BoolTyDesc
  B : Bool -> SystemV ctxt BoolTy

   -- Vectors
  TyVect : (s : Nat)
        -> SystemV ctxt type
        -> SystemV ctxt (VectorTyDesc n type)

  -- Modules Type & Value Constructor...
  TyModule : SystemV ctxt ModuleTyDesc

  EndModule : SystemV ctxt ModuleTy


  -- TypeDef Type & Value Constructors, and Introduction
  TypeDefType : {type : MTy (DATA TYPE)}
             -> (desc : SystemV ctxt type)
                     -> SystemV ctxt (TypeDefTy type)

  TypeDefCTor : {  typeM : MTy (DATA TYPE)}
             -> {  typeV : MTy (DATA VALUE)}
             -> (  type  : SystemV ctxt (TypeDefTy typeM))
             -> (  value : SystemV ctxt                  typeV)
             -> (0 prf   : TyCheckData             typeM typeV)
                        -> SystemV ctxt (TypeDefTy       typeV)

  TypeDef : {lvl      : Level}
         -> {type     : MTy (DATA TYPE)}
         -> {bodyType : MTy (DATA lvl)}
         -> (desc     : SystemV  ctxt    (TypeDefTy type))
         -> (body     : SystemV (ctxt += (TypeDefTy type)) bodyType)
                     -> SystemV ctxt                       bodyType

  -- Ports
  TyPort : {type : MTy (DATA TYPE)}
        -> (desc : SystemV ctxt         type)
        -> (dir  : Direction)
                -> SystemV ctxt (PortTy type dir)

  MkPort : {type  : MTy (DATA TYPE)}
        -> (typeD : SystemV ctxt type)
        -> (dir   : Direction)
                 -> SystemV ctxt (PortVal type dir)

  -- Channels
  TyChan : {type  : MTy (DATA TYPE)}
        -> (typeD : SystemV ctxt type)
                 -> SystemV ctxt (ChanTy type)

  MkChan : {type  : MTy (DATA TYPE)}
        -> (typeD : SystemV ctxt type)
                 -> SystemV ctxt (ChanVal type)

  WriteTo : (chan : SystemV ctxt (ChanVal type))
                 -> SystemV ctxt (PortVal type OUT)

  ReadFrom : (chan : SystemV ctxt (ChanVal type))
                  -> SystemV ctxt (PortVal type IN)

  Drive : {type    : MTy (DATA TYPE)}
       -> (chan    : SystemV ctxt (ChanVal type))
                  -> SystemV ctxt UnitVal

  Catch : {type  : MTy (DATA TYPE)}
       -> (chan : SystemV ctxt (ChanVal type))
               -> SystemV ctxt UnitVal

  -- Runtime wiring decisions
  IfThenElseR : {type     : MTy (DATA TYPE)}
             -> (test     : SystemV ctxt (PortVal type IN))
             -> (whenIsZ  : SystemV ctxt ModuleTy)
             -> (whenNotZ : SystemV ctxt ModuleTy)
                         -> SystemV ctxt ModuleTy

  -- Connect two ports together.
  Connect : {type : MTy (DATA TYPE)}
         -> {dirL, dirR : Direction}
         -> (portL : SystemV ctxt (PortVal type dirL))
         -> (portR : SystemV ctxt (PortVal type dirR))
         -> (prf   : ValidFlow dirL dirR)
                  -> SystemV ctxt UnitVal

  -- Casts
  Cast : {tyA,tyB : MTy (DATA TYPE)}
      -> {dirA,dirB : Direction}
      -> (portA : SystemV ctxt (PortVal tyA dirA))
      -> (prf   : ValidCast (PortVal tyA dirA) (PortVal tyB dirB))
               -> SystemV ctxt (PortVal tyB dirB)

  -- Params
  TyParam : SystemV ctxt ParamTy

  MkParam : (val : Nat) -> SystemV ctxt ParamVal

  ParamOpBool : (op    : Nat -> Nat -> Bool)
             -> (left  : SystemV ctxt ParamVal)
             -> (right : SystemV ctxt ParamVal)
                      -> SystemV ctxt BoolTy

  ParamOpArith : (op    : Nat -> Nat -> Nat)
              -> (left  : SystemV ctxt ParamVal)
              -> (right : SystemV ctxt ParamVal)
                       -> SystemV ctxt ParamVal

  -- Compile time wiring decisions
  IfThenElseC : (test      : SystemV ctxt BoolTy)
             -> (whenTrue  : SystemV ctxt ModuleTy)
             -> (whenFalse : SystemV ctxt ModuleTy)
                          -> SystemV ctxt ModuleTy

  -- Binders
  Let : {  mtypeValue : MTy (IDX VALUE)}
     -> {  bodyType   : MTy (IDX VALUE)}
     -> (  value : SystemV ctxt mtypeValue)
     -> (  body  : SystemV (ctxt += mtypeValue) bodyType)
                -> SystemV  ctxt                bodyType

public export
seq : {b        : MTy (IDX VALUE)}
   -> (this     : SystemV  ctxt    UnitVal)
   -> (thenThis : SystemV (ctxt += UnitVal)  b)
               -> SystemV  ctxt              b
seq this thenThis = App (Func TyUnit thenThis ChkUnit) this
-- --------------------------------------------------------------------- [ EOF ]
