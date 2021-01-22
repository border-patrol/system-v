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

  Func : {body : SystemV (ctxt += paramTy) bodyTy}
              -> Value (Func body)

  TyUnit : Value TyUnit
  MkUnit : Value MkUnit

  TyLogic : Value TyLogic
  Logic   : Value L

  TyVect : Value type -> Value (TyVect s type)
  Vect   : Value V

  TyModule  : Value TyModule
  EndModule : Value EndModule

  TypeDefType : Value desc  -> Value (TypeDefType desc)
  TypeDefCTor : Value value -> Value (TypeDefCTor type value prf)

  TyChan : Value type -> Value (TyChan type)
  MkChan : Value type -> Value (MkChan type)

  TyParam : Value type -> Value (TyParam type)
  MkParam : Value type -> Value (MkParam type)

  TyPort : Value type -> (dir : Direction) -> Value (TyPort type dir)
  MkPort : Value type -> (dir : Direction) -> Value (MkPort type dir)

  Connect : {portL : SystemV ctxt (PortVal type dirL)}
         -> {portR : SystemV ctxt (PortVal type dirR)}
         -> Value portL
         -> Value portR
         -> Value (Connect portL portR prf)

-- --------------------------------------------------------------------- [ EOF ]
