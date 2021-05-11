||| Values in SystemV.Param.
|||
module SystemV.Param.Evaluation.Values

import SystemV.Common.Utilities

import SystemV.Param.Types
import SystemV.Param.Terms

%default total


public export
data Value : SystemV ctxt type -> Type where
  -- [ Types ]

  -- Hardware Specific

  TyPort : Value type -> (dir : Direction) -> Value (TyPort type dir)
  TyChan : Value type -> Value (TyChan type)
  TyUnit : Value TyUnit

  TyNat  : Value TyNat
  TyBool : Value TyBool

  TyModule  : Value TyModule

  -- Data
  DATATYPE : Value DATATYPE
  TyLogic : Value TyLogic
  TyVect : {type : SystemV ctxt typeD}
        -> Value type
        -> IsSucc s
        -> Value (TyVect (MkNat s) type)

  -- [ Terms ]

  -- STLC
  Func : {type : SystemV  ctxt paramTyDesc}
      -> {body : SystemV (ctxt += paramTy) bodyTy}
      -> {prf  : TyCheck paramTyDesc paramTy}
              -> Value (Func type body prf vld)

  FuncP : {typetype : TYPE uty}
       -> {typeterm : TYPE utm}
       -> {type : SystemV ctxt typetype}
       -> {def  : SystemV ctxt typeterm}
       -> {body : SystemV (ctxt += typeterm) bodyTy}
       -> {prf  : Function.ValidTerm (IDX TERM) (FuncParamTy utm typeterm bodyTy)}
       -> (chk  : Default.TyCheck uty utm typetype typeterm)
               -> Value (FuncParam type def body prf chk)

  -- Hardware Specific
  MkNat  : Value (MkNat n)
  MkBool : Value (MkBool b)

  MkUnit : Value MkUnit
  EndModule : Value EndModule

  MkChan : Value type -> Value (MkChan type)

  Drive : (c : Value        chan)
            -> Value (Drive chan)

  Catch : (c : Value        chan)
            -> Value (Catch chan)

  IfThenElseR : Value              cond
             -> Value                   true
             -> Value                        false
             -> Value (IfThenElseR cond true false)

  MkPort : Value type
        -> (dir : Direction)
        -> Value (MkPort type dir)

  Not : {out : SystemV ctxt (PortTy type OUT)}
     -> {i   : SystemV ctxt (PortTy type IN)}
            -> Value out
            -> Value i
            -> Value (Not out i)

  Gate : {out   : SystemV ctxt (PortTy type OUT)}
      -> {ia,ib : SystemV ctxt (PortTy type IN)}
               -> Value out
               -> Value ia
               -> Value ib
               -> Value (Gate kind out ia ib)

  Connect : {portL : SystemV ctxt (PortTy type dirL)}
         -> {portR : SystemV ctxt (PortTy type dirR)}
         -> Value portL
         -> Value portR
         -> Value (Connect portL portR prf)

  -- Seq
  Seq : {left  : SystemV ctxt UnitTy}
     -> {right : SystemV ctxt type}

     -> Value left
     -> Value right
     -> Value (Seq left right)

-- --------------------------------------------------------------------- [ EOF ]
