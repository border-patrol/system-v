module SystemV.HigherOrder.Terms.Substitution

import SystemV.Common.Utilities
import SystemV.HigherOrder.Types

import SystemV.HigherOrder.Terms
import SystemV.HigherOrder.Terms.Renaming

%default total

public export
weakens : (f : {level : Universe}
            -> {type  : TYPE level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : TYPE level}
                 -> Types.Contains (old += type') type
                 -> SystemV (new += type') type)
weakens f (H (Same Refl Refl)) = Var (H (Same Refl Refl))
weakens f (T rest) = rename T (f rest)

namespace General
  public export
  subst : (f : {level : Universe}
            -> {type  : TYPE level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : TYPE level}
                 -> SystemV old type
                 -> SystemV new type)
  -- [ Types ]
  subst f (TyFunc paramTy returnTy prf)
    = TyFunc (subst f paramTy)
             (subst f returnTy)
             prf

  subst f TyUnit
    = TyUnit

  subst f TyModule
    = TyModule

  subst f (TyChan typeD)
    = TyChan (subst f typeD)

  subst f (TyPort desc dir)
    = TyPort (subst f desc)
             dir

  subst f TyLogic
    = TyLogic

  subst f (TyVect s type)
    = TyVect s
             (subst f type)

  -- [ STLC ]
  subst f (Var idx)
    = (f idx)

  subst f (Func type body prf vld)
    = Func (subst          f  type)
           (subst (weakens f) body)
           prf
           vld

  subst f (App func value)
    = App (subst f func)
          (subst f value)

  -- [ Hardware Prims ]
  subst f MkUnit
    = MkUnit

  subst f EndModule
    = EndModule

  subst f (MkPort typeD dir)
    = MkPort (subst f typeD)
             dir

  subst f (MkChan typeD)
    = MkChan (subst f typeD)

  subst f (WriteTo chan)
    = WriteTo (subst f chan)

  subst f (ReadFrom chan)
    = ReadFrom (subst f chan)

  subst f (Drive chan)
    = Drive (subst f chan)

  subst f (Catch chan)
    = Catch (subst f chan)

  subst f (IfThenElseR test whenIsZ whenNotZ)
    = IfThenElseR (subst f test)
                  (subst f whenIsZ)
                  (subst f whenNotZ)

  subst f (Connect portL portR prf)
    = Connect (subst f portL)
              (subst f portR)
              prf

  subst f (Cast portA prf)
    = Cast (subst f portA)
           prf

  subst f (Slice port alpha omega prf)
    = Slice (subst f port)
            alpha
            omega
            prf

  subst f (Index n port prf)
    = Index n
            (subst f port)
            prf

  subst f (Not portO portI)
    = Not (subst f portO)
          (subst f portI)

  subst f (Gate kind portO portIA portIB)
    = Gate kind (subst f portO)
                (subst f portIA)
                (subst f portIB)

  subst f (Let value body)
    = Let (subst          f  value)
          (subst (weakens f) body)

  subst f (Seq left right)
    = Seq (subst f left)
          (subst f right)

namespace Single
  public export
  apply : {levelA : Universe}
       -> {typeA  : TYPE levelA}
       -> (this   : SystemV ctxt typeB)
       -> (idx    : Contains (ctxt += typeB) typeA)
                 -> SystemV ctxt typeA
  apply this (H (Same Refl Refl)) = this
  apply this (T rest) = Var rest

  public export
  subst : {levelA,levelB : Universe}
       -> {typeA         : TYPE levelA}
       -> {typeB         : TYPE levelB}
       -> (this          : SystemV  ctxt           typeB)
       -> (inThis        : SystemV (ctxt += typeB) typeA)
                        -> SystemV  ctxt           typeA
  subst {ctxt} {typeA} {typeB} {levelA} {levelB} this inThis
    = General.subst (apply this) inThis

-- --------------------------------------------------------------------- [ EOF ]
