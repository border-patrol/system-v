||| Values in SystemV.
|||
module SystemV.Values

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms

%default total

public export
data Value : SystemV ctxt type -> Type where
  TyFunc : {param  : SystemV ctxt pty}
        -> {return : SystemV ctxt rty}
        -> Value param
        -> Value return
        -> Value (TyFunc param return)

  Func : {type : SystemV  ctxt paramTyDesc}
      -> {body : SystemV (ctxt += paramTy) bodyTy}
      -> {prf  : TyCheck paramTyDesc paramTy}
              -> Value (Func type body prf)

  TyUnit : Value TyUnit
  MkUnit : Value MkUnit

  TyLogic : Value TyLogic

  TyVect : (s : Whole) -> {type : SystemV ctxt typeD} -> Value type -> Value (TyVect s type)

  TyBool : Value TyBool
  B      : Value (B b)

  TyModule  : Value TyModule
  EndModule : Value EndModule

  TypeDefType : Value desc  -> Value (TypeDefType desc)
  TypeDefCTor : Value value -> Value (TypeDefCTor type value prf)

  TyChan : Value type -> Value (TyChan type)
  MkChan : Value type -> Value (MkChan type)

  Drive : (c    : Value chan )
               -> Value (Drive chan)

  Catch : Value chan -> Value (Catch chan)

  IfThenElseR : Value cond
             -> Value true
             -> Value false
             -> Value (IfThenElseR cond true false)

  TyParam : Value TyParam
  MkParam : Value (MkParam val)

  TyPort : Value type -> (dir : Direction) -> Value (TyPort type dir)
  MkPort : Value type -> (dir : Direction) -> Value (MkPort type dir)

  Connect : {portL : SystemV ctxt (PortVal type dirL)}
         -> {portR : SystemV ctxt (PortVal type dirR)}
         -> Value portL
         -> Value portR
         -> Value (Connect portL portR prf)


-- --------------------------------------------------------------------- [ EOF ]
