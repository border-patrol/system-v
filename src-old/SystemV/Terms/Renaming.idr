module SystemV.Terms.Renaming

import Data.Vect

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms

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
           -> {type  : MTy level}
                    -> Types.Contains old type
                    -> Types.Contains new type)
      -> ({level : Universe}
       -> {type : MTy level}
       -> SystemV old type
       -> SystemV new type)

-- STLC
rename f (Var idx)            = Var (f idx)
rename f (Func type body prf) = Func (rename f type) (rename (weaken f) body) prf
rename f (App func param)     = App (rename f func) (rename f param)
rename f (TyFunc param body)
  = TyFunc (rename f param) (rename f body)

-- Unit
rename f TyUnit = TyUnit
rename f MkUnit = MkUnit

-- Data Types
rename f TyLogic = TyLogic
rename f (TyVect s type) = TyVect s (rename f type)

rename f TyBool = TyBool
rename f (B b)  = B b

-- Modules
rename f TyModule  = TyModule
rename f EndModule = EndModule

-- TypeDefs
rename f (TypeDefType desc) = TypeDefType (rename f desc)
rename f (TypeDefCTor type value prf)
    = TypeDefCTor (rename f type)
                  (rename f value)
                  prf

rename f (TypeDef type body)
    = TypeDef (rename f type)
              (rename (weaken f) body)

-- Ports
rename f (TyPort desc dir) = TyPort (rename f desc) dir
rename f (MkPort type dir) = MkPort (rename f type) dir

-- Channels
rename f (TyChan desc) = TyChan (rename f desc)
rename f (MkChan type) = MkChan (rename f type)

rename f (WriteTo  chan) = WriteTo  (rename f chan)
rename f (ReadFrom chan) = ReadFrom (rename f chan)

rename f (Drive chan)
  = Drive (rename f chan)

rename f (Catch chan) = Catch (rename f chan)

-- RunTime wiring
rename f (IfThenElseR cond true false)
  = IfThenElseR (rename f cond)
                (rename f true)
                (rename f false)

-- Connections
rename f (Connect portL portR prf)
  = Connect (rename f portL)
            (rename f portR)
            prf

-- Casting
rename f (Cast this prf) = Cast (rename f this) prf

-- Slicing
rename f (Slice this a o prf) = Slice (rename f this) a o prf

-- Gates
rename f (Not portO portI)
  = Not (rename f portO)
        (rename f portI)

rename f (Gate kind portO portIA portIB)
  = Gate kind (rename f portO)
              (rename f portIA)
              (rename f portIB)

-- Params
rename f TyParam       = TyParam
rename f (MkParam val) = MkParam val

rename f (ParamOpBool op l r)
  = ParamOpBool op (rename f l) (rename f r)

rename f (ParamOpNot p)
  = ParamOpNot (rename f p)

rename f (IfThenElseC cond true false)
  = IfThenElseC (rename f cond)
                (rename f true)
                (rename f false)
-- Binders
rename f (Let value body)
    = Let (rename f value)
          (rename (weaken f) body)

-- --------------------------------------------------------------------- [ EOF ]
