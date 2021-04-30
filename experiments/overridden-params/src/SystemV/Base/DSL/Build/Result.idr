module SystemV.Base.DSL.Build.Result

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

import        SystemV.Common.Utilities

import        SystemV.Base.Types
import        SystemV.Base.Terms

import        SystemV.Base.DSL.AST
import        SystemV.Base.DSL.Build.Context



%default total

public export
data Result : (lvls : Universes)
           -> (ctxt : Context lvls)
                   -> Type
  where
    Res : {ctxt : Context lvls}
       -> (u    : Universe)
       -> (type : TYPE u)
       -> (term : SystemV ctxt type)
               -> Result lvls ctxt


-- --------------------------------------------------------------------- [ EOF ]
