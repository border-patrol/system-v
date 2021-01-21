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

  Func : {paramTy, bodyTy : MTy (IDX VALUE)}
      -> (term : SystemV (ctxt +=         paramTy) bodyTy)
              -> SystemV  ctxt    (FuncTy paramTy  bodyTy)

  App : {paramTy, bodyTy : MTy (IDX VALUE)}
     -> (func  : SystemV ctxt (FuncTy paramTy  bodyTy))
     -> (value : SystemV ctxt         paramTy)
              -> SystemV ctxt                   bodyTy

  TyFunc : {paramMTy, returnMTy : MTy (IDX TYPE)}
        -> (paramTy  : SystemV ctxt paramMTy)
        -> (returnTy : SystemV ctxt returnMTy)
                    -> SystemV ctxt (FuncTy paramMTy returnMTy)

  -- Logic Type & Value Constructors
  TyLogic : SystemV ctxt LogicTyDesc

  L : SystemV ctxt LogicTy

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


  -- Connect two ports together.
  Connect : {type : MTy (DATA TYPE)}
         -> {dirL, dirR : Direction}
         -> (portL : SystemV ctxt (PortVal type dirL))
         -> (portR : SystemV ctxt (PortVal type dirR))
         -> (prf   : ValidFlow dirL dirR)
                  -> SystemV ctxt UnityTy

  -- Params
  TyParam : {type  : MTy (DATA TYPE)}
         -> (typeD : SystemV ctxt          type)
                  -> SystemV ctxt (ParamTy type)

  MkParam : {type  : MTy (DATA TYPE)}
         -> (typeD : SystemV ctxt           type)
                  -> SystemV ctxt (ParamVal type)

  -- Binders
  Let : {  mtypeType  : MTy (IDX TYPE)}
     -> {  mtypeValue : MTy (IDX VALUE)}
     -> {  bodyType   : MTy (IDX VALUE)}
     -> (  type  : SystemV ctxt mtypeType)
     -> (  value : SystemV ctxt mtypeValue)
     -> (0 prf   : TyCheck mtypeType mtypeValue)
     -> (  body  : SystemV (ctxt += mtypeValue) bodyType)
                -> SystemV  ctxt                bodyType

-- --------------------------------------------------------------------- [ EOF ]
