module SystemV.Core.DSL.Build.Result

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

import        SystemV.Core.Types
import        SystemV.Core.Terms

import        SystemV.Core.DSL.AST
import        SystemV.Core.DSL.Build.Context



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
