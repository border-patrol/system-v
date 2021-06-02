||| Values in SystemV.Params.
|||
module SystemV.Params.Evaluation.Values

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

%default total


public export
data Value : SystemV ctxt type -> Type where
  -- [ Types ]

  -- Hardware Specific

  TyPort : Value type -> (dir : Direction) -> Value (TyPort fc type dir)
  TyChan : Value type -> Value (TyChan fc type)
  TyUnit : Value (TyUnit fc)

  TyNat  : Value (TyNat fc)
  TyBool : Value (TyBool fc)

  TyModule  : Value (TyModule fc)

  -- Data
  DATATYPE : Value (DATATYPE fc)
  TyLogic : Value (TyLogic fc)
  TyVect : {type : SystemV ctxt DATATERM}
        -> Value type
        -> IsSucc s
        -> Value (TyVect fc (MkNat fcn s) type)

  -- [ Terms ]

  -- STLC
  Func : {type : SystemV  ctxt paramTyDesc}
      -> {body : SystemV (ctxt += paramTy) bodyTy}
      -> {prf  : TyCheck paramTyDesc paramTy}
              -> Value (Func fc type body prf vld)

  FuncP : {typetype : TYPE uty}
       -> {typeterm : TYPE utm}
       -> {type : SystemV ctxt typetype}
       -> {def  : SystemV ctxt typeterm}
       -> {body : SystemV (ctxt += typeterm) bodyTy}
       -> {prf  : Function.ValidTerm (IDX TERM) (FuncParamTy utm typeterm bodyTy)}
       -> (chk  : Default.TyCheck uty utm typetype typeterm)
               -> Value (FuncParam fc type def body prf chk)

  -- Hardware Specific
  MkNat  : Value (MkNat fc n)
  MkBool : Value (MkBool fc b)

  MkUnit : Value (MkUnit fc)
  EndModule : Value (EndModule fc)

  MkChan : Value type -> Value (MkChan fc type)

  Drive : (c : Value           chan)
            -> Value (Drive fc chan)

  Catch : (c : Value           chan)
            -> Value (Catch fc chan)

  IfThenElseR : Value                cond
             -> Value                     true
             -> Value                          false
             -> Value (IfThenElseR fc cond true false)

  MkPort : Value type
        -> (dir : Direction)
        -> Value (MkPort fc type dir)

  Not : {out : SystemV ctxt (PortTy OUT)}
     -> {i   : SystemV ctxt (PortTy IN)}
            -> Value out
            -> Value i
            -> Value (Not fc out i)

  Gate : {out   : SystemV ctxt (PortTy OUT)}
      -> {ia,ib : SystemV ctxt (PortTy IN)}
               -> Value out
               -> Value ia
               -> Value ib
               -> Value (Gate fc kind out ia ib)

  Connect : {portL : SystemV ctxt (PortTy dirL)}
         -> {portR : SystemV ctxt (PortTy dirR)}
         -> Value portL
         -> Value portR
         -> Value (Connect fc portL portR prf)

  -- Seq
  Seq : {left  : SystemV ctxt UnitTy}
     -> {right : SystemV ctxt type}

     -> Value left
     -> Value right
     -> Value (Seq fc left right prf)

-- --------------------------------------------------------------------- [ EOF ]
