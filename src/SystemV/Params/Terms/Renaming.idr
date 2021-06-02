module SystemV.Params.Terms.Renaming

import Data.Vect

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
rename f (DATATYPE fc)
  = (DATATYPE fc)

rename f (TyUnit fc)
  = (TyUnit fc)

rename f (TyNat fc)
  = (TyNat fc)

rename f (TyBool fc)
  = (TyBool fc)

rename f (TyModule fc)
  = (TyModule fc)

rename f (TyChan fc typeD)
  = TyChan fc (rename f typeD)

rename f (TyPort fc desc dir)
  = TyPort fc
           (rename f desc)
           dir

rename f (TyLogic fc)
  = (TyLogic fc)

rename f (TyVect fc s type)
  = TyVect fc
           (rename f s)
           (rename f type)

-- [ STLC ]
rename f (Var fc idx)
  = Var fc (f idx)

rename f (Func fc type body chk prf)
  = Func fc
         (rename         f  type)
         (rename (weaken f) body)
         chk
         prf

rename f (App fc func value)
  = App fc
        (rename f func)
        (rename f value)


rename f (FuncParam fc type def body prf chk)
  = FuncParam fc
              (rename         f  type)
              (rename         f  def)
              (rename (weaken f) body)
              prf
              chk

rename f (AppDef fc func)
  = AppDef fc (rename f func)


rename f (AppOver fc func value)
  = AppOver fc
            (rename f func)
            (rename f value)


-- [ Hardware Prims ]
rename f (MkUnit fc)
  = (MkUnit fc)

rename f (EndModule fc)
  = (EndModule fc)

rename f (MkPort fc typeD dir)
  = MkPort fc
           (rename f typeD)
           dir

rename f (MkChan fc typeD)
  = MkChan fc (rename f typeD)

rename f (WriteTo fc chan)
  = WriteTo fc (rename f chan)

rename f (ReadFrom fc chan)
  = ReadFrom fc (rename f chan)

rename f (Drive fc  chan)
  = Drive fc (rename f chan)

rename f (Catch fc chan)
  = Catch fc (rename f chan)

rename f (IfThenElseR fc test whenIsZ whenNotZ)
  = IfThenElseR fc
                (rename f test)
                (rename f whenIsZ)
                (rename f whenNotZ)

rename f (Connect fc portL portR prf)
  = Connect fc
            (rename f portL)
            (rename f portR)
            prf


rename f (Cast fc portA type dir prf)
  = Cast fc
         (rename f portA)
         (rename f type)
         dir
         prf

rename f (Slice fc port alpha omega)
  = Slice fc
          (rename f port)
          (rename f alpha)
          (rename f omega)


rename f (Index fc n port)
  = Index fc
          (rename f n)
          (rename f port)

rename f (Size fc port)
  = Size fc (rename f port)

rename f (Not fc portO portI)
  = Not fc
        (rename f portO)
        (rename f portI)

rename f (Gate fc kind portO portIA portIB)
  = Gate fc kind (rename f portO)
                 (rename f portIA)
                 (rename f portIB)

rename f (Let fc value body prf)
  = Let fc
        (rename         f  value)
        (rename (weaken f) body)
        prf

rename f (Seq fc left right prf)
  = Seq fc
        (rename f left)
        (rename f right)
        prf

rename f (MkNat fc n)
  = MkNat fc n

rename f (MkBool fc b)
  = MkBool fc b

rename f (IfThenElseC fc test whenIsZ whenNotZ)
  = IfThenElseC fc
                (rename f test)
                (rename f whenIsZ)
                (rename f whenNotZ)

rename f (NatOpArith fc op left right)
  = NatOpArith fc op
               (rename f left)
               (rename f right)

rename f (NatOpCmp fc op left right)
  = NatOpCmp fc op
             (rename f left)
             (rename f right)


rename f (BoolOpBin fc op left right)
  = BoolOpBin fc
              op
              (rename f left)
              (rename f right)

rename f (BoolNot fc n)
  = BoolNot fc (rename f n)

rename f (For fc counter body)
  = For fc
        (rename f counter)
        (rename (weaken f) body)
-- --------------------------------------------------------------------- [ EOF ]
