module SystemV.Params.Terms.Renaming

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

%default total

public export
weaken : (func : Types.Contains old type
              -> Types.Contains new type)
      -> (Contains (old += type') type
       -> Types.Contains (new += type') type)

weaken func (H (Same Refl Refl)) = H (Same Refl Refl)
weaken func (T rest) = T (func rest)

public export
rename : (f : {level : Universe}
           -> {type  : TYPE level}
                    -> Types.Contains old type
                    -> Types.Contains new type)
      -> ({level : Universe}
       -> {type : TYPE level}
       -> SystemV old type
       -> SystemV new type)

-- [ Types ]
rename f (TyFunc paramTy returnTy prf)
  = TyFunc (rename f paramTy)
           (rename f returnTy)
           prf

rename f (TyFuncD paramTy returnTy vld)
  = TyFuncD (rename f paramTy)
            (rename f returnTy)
            vld

rename f TyUnit
  = TyUnit

rename f (TyNat n)
  = TyNat n

rename f TyModule
  = TyModule

rename f (TyChan typeD)
  = TyChan (rename f typeD)

rename f (TyPort desc dir)
  = TyPort (rename f desc)
           dir

rename f (TyTypeDef desc)
  = TyTypeDef (rename f desc)

rename f TyLogic
  = TyLogic

rename f TyBool
  = TyBool

rename f (TyVect s type)
  = TyVect s
           (rename f type)

rename f (TyOverride inner)
  = TyOverride (rename f inner)


-- [ STLC ]
rename f (Var idx)
  = Var (f idx)

rename f (Func type body prf vld)
  = Func (rename         f  type)
         (rename (weaken f) body)
         prf
         vld

rename f (FuncD ty def body prf vld)
  = FuncD (rename         f  ty)
          (rename         f  def)
          (rename (weaken f) body)
          prf
          vld

rename f (App func value)
  = App (rename f func)
        (rename f value)

rename f (AppDef func)
  = AppDef (rename f func)

rename f (AppOver func value)
  = AppOver (rename f func)
            (rename f value)

-- Unit

rename f MkUnit
  = MkUnit

rename f EndModule
  = EndModule

rename f (MkPort typeD dir)
  = MkPort (rename f typeD)
           dir

rename f (MkChan typeD)
  = MkChan (rename f typeD)

rename f (WriteTo chan)
  = WriteTo (rename f chan)

rename f (ReadFrom chan)
  = ReadFrom (rename f chan)

rename f (Drive chan)
  = Drive (rename f chan)

rename f (Catch chan)
  = Catch (rename f chan)

rename f (IfThenElseR test whenIsZ whenNotZ)
  = IfThenElseR (rename f test)
                (rename f whenIsZ)
                (rename f whenNotZ)

rename f (Connect portL portR prf)
  = Connect (rename f portL)
            (rename f portR)
            prf

rename f (Cast portA prf)
  = Cast (rename f portA)
         prf

rename f (Slice port alpha omega prf)
  = Slice (rename f port)
          (rename f alpha)
          (rename f omega)
          prf

rename f (Index n port prf)
  = Index (rename f n)
          (rename f port)
          prf

rename f (Size port)
  = Size (rename f port)

rename f (Not portO portI)
  = Not (rename f portO)
        (rename f portI)

rename f (Gate kind portO portIA portIB)
  = Gate kind (rename f portO)
              (rename f portIA)
              (rename f portIB)

rename f (Let value body)
  = Let (rename         f  value)
        (rename (weaken f) body)

rename f (Seq left right)
  = Seq (rename f left)
        (rename f right)

rename f (MkNat n)
  = MkNat n

rename f (NatOverride n)
  = NatOverride n

rename f (OpArith op left right)
  = OpArith op
            (rename f left)
            (rename f right)

rename f (OpBool op left right)
  = OpBool op
           (rename f left)
           (rename f right)

rename f (OpCmp op left right)
  = OpCmp op
          (rename f left)
          (rename f right)

rename f (OpNot bool)
  = OpNot (rename f bool)

rename f (IfThenElseC test whenT whenF)
  = IfThenElseC (rename f test)
                (rename f whenT)
                (rename f whenF)

rename f (B b)
  = B b

-- --------------------------------------------------------------------- [ EOF ]
