module SystemV.Params.Terms.Substitution

import SystemV.Common.Utilities
import SystemV.Params.Types

import SystemV.Params.Terms
import SystemV.Params.Terms.Renaming

%default total

public export
weakens : FC
       -> (f : {level : Universe}
            -> {type  : TYPE level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : TYPE level}
                 -> Types.Contains (old += type') type
                 -> SystemV (new += type') type)
weakens fc f (H (Same Refl Refl)) = Var fc (H (Same Refl Refl))
weakens fc f (T rest) = rename T (f rest)

namespace General
  public export
  subst : FC
       -> (f : {level : Universe}
            -> {type  : TYPE level}
                     -> Types.Contains old type
                     -> SystemV new type)
       -> ({level : Universe}
        -> {type  : TYPE level}
                 -> SystemV old type
                 -> SystemV new type)
  -- [ Types ]
  subst l f (DATATYPE fc)
    = (DATATYPE l)

  subst l f (TyUnit fc)
    = (TyUnit fc)

  subst l f (TyNat fc)
    = (TyNat l)

  subst l f (TyBool fc)
    = (TyBool l)

  subst l f (TyModule fc)
    = (TyModule l)

  subst l f (TyChan fc typeD)
    = TyChan fc (subst l f typeD)

  subst l f (TyPort fc desc dir)
    = TyPort fc
             (subst l f desc)
             dir

  subst l f (TyLogic fc)
    = (TyLogic l)

  subst l f (TyVect fc s type)
    = TyVect fc
             (subst l f s)
             (subst l f type)

  -- [ STLC ]
  subst _ f (Var _ idx)
    = (f idx)

  subst l f (Func fc type body chk prf)
    = Func fc
           (subst            l f  type)
           (subst l (weakens l f) body)
           chk
           prf

  subst l f (App fc func value)
    = App fc
          (subst l f func)
          (subst l f value)

  subst l f (FuncParam fc type def body prf chk)
    = FuncParam fc
                (subst            l f  type)
                (subst            l f  def)
                (subst l (weakens l f) body)
                prf
                chk

  subst l f (AppDef fc func)
    = AppDef fc (subst l f func)


  subst l f (AppOver fc func value )
    = AppOver fc
              (subst l f func)
              (subst l f value)


  -- [ Hardware Prims ]
  subst l f (MkUnit fc)
    = (MkUnit fc)

  subst l f (EndModule fc)
    = (EndModule fc)

  subst l f (MkPort fc typeD dir)
    = MkPort fc
             (subst l f typeD)
             dir

  subst l f (MkChan fc typeD)
    = MkChan fc (subst l f typeD)

  subst l f (WriteTo fc chan)
    = WriteTo fc (subst l f chan)

  subst l f (ReadFrom fc chan)
    = ReadFrom fc (subst l f chan)

  subst l f (Drive fc chan)
    = Drive fc (subst l f chan)

  subst l f (Catch fc chan)
    = Catch fc (subst l f chan)

  subst l f (IfThenElseR fc test whenIsZ whenNotZ)
    = IfThenElseR fc
                  (subst l f test)
                  (subst l f whenIsZ)
                  (subst l f whenNotZ)

  subst l f (Connect fc portL portR prf)
    = Connect fc
              (subst l f portL)
              (subst l f portR)
              prf

  subst l f (Cast fc portA type dir prf)
    = Cast fc
           (subst l f portA)
           (subst l f type)
           dir
           prf

  subst l f (Slice fc port alpha omega)
    = Slice fc
            (subst l f port)
            (subst l f alpha)
            (subst l f omega)


  subst l f (Index fc n port)
    = Index fc
            (subst l f n)
            (subst l f port)


  subst l f (Size fc port)
    = Size fc (subst l f port)

  subst l f (Not fc portO portI)
    = Not fc
          (subst l f portO)
          (subst l f portI)

  subst l f (Gate fc kind portO portIA portIB)
    = Gate fc kind (subst l f portO)
                   (subst l f portIA)
                   (subst l f portIB)

  subst l f (Let fc value body prf)
    = Let fc
          (subst            l f  value)
          (subst l (weakens l f) body)
          prf

  subst l f (Seq fc left right prf)
    = Seq fc
          (subst l f left)
          (subst l f right)
          prf

  subst l f (MkNat fc n)
    = MkNat l n

  subst l f (MkBool fc b)
    = MkBool l b

  subst l f (IfThenElseC fc test whenIsZ whenNotZ)
    = IfThenElseC fc (subst l f test)
                     (subst l f whenIsZ)
                     (subst l f whenNotZ)

  subst l f (NatOpArith fc op left right)
    = NatOpArith fc
                 op
                 (subst l f left)
                 (subst l f right)

  subst l f (NatOpCmp fc op left right)
    = NatOpCmp fc
               op
               (subst l f left)
               (subst l f right)

  subst l f (BoolOpBin fc op left right)
    = BoolOpBin fc
                op
                (subst l f left)
                (subst l f right)

  subst l f (BoolNot fc n)
    = BoolNot fc (subst l f n)

  subst l f (For fc counter body)
    = For fc
          (subst l            f counter)
          (subst l (weakens l f) body)

namespace Single
  public export
  apply : {levelA : Universe}
       -> {typeA  : TYPE levelA}
       -> FC
       -> (this   : SystemV ctxt typeB)
       -> (idx    : Types.Contains (ctxt += typeB) typeA)
                 -> SystemV ctxt typeA
  apply _  this (H (Same Refl Refl)) = this
  apply fc this (T rest) = Var fc rest

  public export
  subst : {levelA,levelB : Universe}
       -> {typeA         : TYPE levelA}
       -> {typeB         : TYPE levelB}
       -> (this          : SystemV  ctxt           typeB)
       -> (inThis        : SystemV (ctxt += typeB) typeA)
                        -> SystemV  ctxt           typeA
  subst {ctxt} {typeA} {typeB} {levelA} {levelB} this inThis
    = General.subst (getFC this) (apply (getFC this) this) inThis

-- --------------------------------------------------------------------- [ EOF ]
