||| Values in SystemV.Annotated.
|||
module SystemV.Annotated.Values

import SystemV.Common.Utilities

import SystemV.Annotated.Types
import SystemV.Annotated.Terms

%default total

public export
data Value : SystemV ctxt type -> Type where
  -- [ Types ]

  -- Hardware Specific

  TyPort : Value type -> Value (TyPort type dir sense intent)
  TyChan : Value type -> Value (TyChan type sense intent)
  TyUnit : Value TyUnit


  TyModule  : Value TyModule

  -- Data
  TyLogic : Value TyLogic
  TyVect : (s : Whole)
        -> {type : SystemV ctxt typeD}
        -> Value type
        -> Value (TyVect s type)

  -- [ Terms ]

  -- STLC
  Func : {type : SystemV  ctxt paramTyDesc}
      -> {body : SystemV (ctxt += paramTy) bodyTy}
      -> {prf  : TyCheck paramTyDesc paramTy}
              -> Value (Func type body prf vld)

  -- Hardware Specific

  MkUnit : Value MkUnit
  EndModule : Value EndModule

  MkChan : Value type -> Value (MkChan type sense intent)

  Drive : (c : Value        chan)
            -> Value (Drive s i chan)

  Catch : (c : Value        chan)
            -> Value (Catch chan)

  IfThenElseR : Value              cond
             -> Value                   true
             -> Value                        false
             -> Value (IfThenElseR cond true false)


  MkPort : Value type
        -> Value (MkPort type dir sense intent)

  Not : {out : SystemV ctxt (PortTy type OUT sense intent)}
     -> {i   : SystemV ctxt (PortTy type IN  sense intent)}
            -> Value out
            -> Value i
            -> Value (Not out i)

  Gate : {out   : SystemV ctxt (PortTy type OUT sense intent)}
      -> {ia,ib : SystemV ctxt (PortTy type IN sense intent)}
               -> Value out
               -> Value ia
               -> Value ib
               -> Value (Gate kind out ia ib)

  Connect : {portL : SystemV ctxt (PortTy type dirL sense intent)}
         -> {portR : SystemV ctxt (PortTy type dirR sense intent)}
         -> {prf   : ValidFlow dirL dirR}
         -> Value portL
         -> Value portR
         -> Value (Connect portL portR prf)

  -- Seq
  Seq : {left  : SystemV ctxt UnitTy}
     -> {right : SystemV ctxt type}

     -> Value left
     -> Value right
     -> Value (Seq left right prf)

-- --------------------------------------------------------------------- [ EOF ]
