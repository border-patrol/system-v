module SystemV.Params.Terms.Substitution

import SystemV.Common.Utilities

import SystemV.Params.Types

import SystemV.Params.Terms
import SystemV.Params.Terms.Renaming

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

  subst f (TyFuncD paramTy returnTy vld)
    = TyFuncD (subst f paramTy)
              (subst f returnTy)
              vld

  subst f TyUnit
    = TyUnit

  subst f (TyNat n)
    = TyNat n

  subst f TyBool
    = TyBool

  subst f TyModule
    = TyModule

  subst f (TyChan typeD)
    = TyChan (subst f typeD)

  subst f (TyPort desc dir)
    = TyPort (subst f desc)
             dir

  subst f (TyTypeDef desc)
    = TyTypeDef (subst f desc)

  subst f TyLogic
    = TyLogic

  subst f (TyVect s type)
    = TyVect s
             (subst f type)

  subst f (TyOverride inner)
    = TyOverride (subst f inner)

  -- [ STLC ]
  subst f (Var idx)
    = (f idx)

  subst f (Func type body prf vld)
    = Func (subst          f  type)
           (subst (weakens f) body)
           prf
           vld

  subst f (FuncD x def body prf vld)
    = FuncD (subst          f  x)
            (subst          f def)
            (subst (weakens f) body)
            prf
            vld

  subst f (App func value)
    = App (subst f func)
          (subst f value)

  subst f (AppDef func)
    = AppDef (subst f func)

  subst f (AppOver func value)
    = AppOver (subst f func)
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
            (subst f alpha)
            (subst f omega)
            prf

  subst f (Index n port prf)
    = Index (subst f n)
            (subst f port)
            prf

  subst f (Size port)
    = Size (subst f port)

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

  subst f (MkNat n)
    = MkNat n

  subst f (NatOverride n)
    = NatOverride n

  subst f (OpArith op left right)
    = OpArith op
              (subst f left)
              (subst f right)

  subst f (OpCmp op left right)
    = OpCmp op
            (subst f left)
            (subst f right)

  subst f (OpBool op left right)
    = OpBool op
             (subst f left)
             (subst f right)

  subst f (OpNot bool)
    = OpNot (subst f bool)

  subst f (IfThenElseC test whenIsZ whenNotZ)
    = IfThenElseC (subst f test)
                  (subst f whenIsZ)
                  (subst f whenNotZ)

  subst f (B b)
    = B b

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
