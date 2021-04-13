||| Values in SystemV.
|||
module SystemV.Evaluation.Values

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms

%default total

public export
data Value : SystemV ctxt type -> Type where
  -- [ Types ]

  -- STLC
  TyFunc : {param  : SystemV ctxt pty}
        -> {return : SystemV ctxt rty}

        -> Value param
        -> Value return
        -> Value (TyFunc param return prf)

  -- Hardware Specific

  TyPort : Value type -> (dir : Direction) -> Value (TyPort type dir)
  TyChan : Value type -> Value (TyChan type)
  TyUnit : Value TyUnit


  TyModule  : Value TyModule
  TyNat     : Value (TyNat n)

  -- Data
  TyLogic : Value TyLogic
  TyVect : (s : Whole)
        -> {type : SystemV ctxt typeD}
        -> Value type
        -> Value (TyVect s type)
  TyTypeDef : Value desc  -> Value (TyTypeDef desc)

  -- [ Terms ]

  -- STLC
  Func : {type : SystemV  ctxt paramTyDesc}
      -> {body : SystemV (ctxt += paramTy) bodyTy}
      -> {prf  : TyCheck paramTyDesc paramTy}
              -> Value (Func type body prf vld)

  -- Hardware Specific

  MkNat  : Value (MkNat n)
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
