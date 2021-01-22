module SystemV.Terms.Substitution

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms
import SystemV.Terms.Renaming

%default total

public export
weakens : (f : {level : Universe}
            -> {type  : MTy level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : MTy level}
                 -> Types.Contains (old += type') type
                 -> SystemV (new += type') type)
weakens f H = Var H
weakens f (T rest) = rename T (f rest)

-- general substitute
namespace General
  public export
  subst : (f : {level : Universe}
            -> {type  : MTy level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : MTy level}
                 -> SystemV old type
                 -> SystemV new type)

  -- STLC
  subst f (Var idx)      = f idx
  subst f (Func body)    = Func (subst (weakens f) body)
  subst f (App func var) = App (subst f func) (subst f var)
  subst f (TyFunc param return)
    = TyFunc (subst f param) (subst f return)

  -- Unit
  subst f TyUnit = TyUnit
  subst f MkUnit = MkUnit

  -- Data Types & Values
  subst f TyLogic = TyLogic
  subst f L = L

  -- Vect
  subst f (TyVect s type) = TyVect s (subst f type)
  subst f V = V

  -- Modules
  subst f TyModule  = TyModule
  subst f EndModule = EndModule

  -- TypeDefs
  subst f (TypeDefCTor type value prf)
      = TypeDefCTor (subst f type) (subst f value) prf

  subst f (TypeDefType desc) = TypeDefType (subst f desc)
  subst f (TypeDef desc body)
      = TypeDef (subst f desc) (subst (weakens f) body)

  -- Ports
  subst f (TyPort desc dir) = TyPort (subst f desc) dir
  subst f (MkPort type dir) = MkPort (subst f type) dir

  -- Chans
  subst f (TyChan   desc) = TyChan   (subst f desc)
  subst f (MkChan   type) = MkChan   (subst f type)
  subst f (WriteTo  chan) = WriteTo  (subst f chan)
  subst f (ReadFrom chan) = ReadFrom (subst f chan)

  -- Connections
  subst f (Connect portL portR prf)
    = Connect (subst f portL) (subst f portR) prf

  -- Params
  subst f (TyParam desc) = TyParam (subst f desc)
  subst f (MkParam type) = MkParam (subst f type)

  -- Bindings
  subst f (Let type value prf body)
      = Let (subst f type)
            (subst f value)
            prf
            (subst (weakens f) body)

namespace Single
  public export
  apply : {levelA : Universe}
       -> {typeA  : MTy levelA}
       -> (this   : SystemV ctxt typeB)
       -> (idx    : Contains (ctxt += typeB) typeA)
                 -> SystemV ctxt typeA
  apply this H = this
  apply this (T rest) = Var rest

  public export
  subst : {levelA,levelB : Universe}
       -> {typeA         : MTy levelA}
       -> {typeB         : MTy levelB}
       -> (this          : SystemV  ctxt           typeB)
       -> (inThis        : SystemV (ctxt += typeB) typeA)
                        -> SystemV  ctxt           typeA
  subst {ctxt} {typeA} {typeB} {levelA} {levelB} this inThis
    = General.subst (apply this) inThis

-- --------------------------------------------------------------------- [ EOF ]
