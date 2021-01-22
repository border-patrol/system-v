module SystemV.Terms.Renaming

import SystemV.Utilities
import SystemV.Types
import SystemV.Terms

%default total

public export
weaken : (func : Types.Contains old type
              -> Types.Contains new type)
      -> (Contains (old += type') type
       -> Types.Contains (new += type') type)

weaken func H = H
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
rename f (Var idx)        = Var (f idx)
rename f (Func body)      = Func (rename (weaken f) body)
rename f (App func param) = App (rename f func) (rename f param)
rename f (TyFunc param body)
  = TyFunc (rename f param) (rename f body)

-- Unit
rename f TyUnit = TyUnit
rename f MkUnit = MkUnit

-- Data Types & Values
rename f TyLogic = TyLogic
rename f L = L

-- Vectors
rename f (TyVect s type) = TyVect s (rename f type)
rename f V = V


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

-- Connections
rename f (Connect portL portR prf)
  = Connect (rename f portL)
            (rename f portR)
            prf

-- Params
rename f (TyParam desc) = TyParam (rename f desc)
rename f (MkParam type) = MkParam (rename f type)

-- Binders
rename f (Let type value prf body)
    = Let (rename f type)
          (rename f value)
          prf
          (rename (weaken f) body)

-- --------------------------------------------------------------------- [ EOF ]
