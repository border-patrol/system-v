module SystemV.Core.Terms.Renaming

import Data.Vect

import SystemV.Common.Utilities
import SystemV.Core.Types
import SystemV.Core.Terms

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

rename f TyUnit
  = TyUnit

rename f TyModule
  = TyModule

rename f (TyChan typeD)
  = TyChan (rename f typeD)

rename f (TyPort desc dir)
  = TyPort (rename f desc)
           dir

rename f TyLogic
  = TyLogic

rename f (TyVect s type)
  = TyVect s
           (rename f type)

-- [ STLC ]
rename f (Var idx)
  = Var (f idx)

rename f (Func type body prf vld)
  = Func (rename         f  type)
         (rename (weaken f) body)
         prf
         vld

rename f (App func value)
  = App (rename f func)
        (rename f value)

-- [ Hardware Prims ]
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
          alpha
          omega
          prf

rename f (Index n port prf)
  = Index n
          (rename f port)
          prf

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

-- --------------------------------------------------------------------- [ EOF ]
