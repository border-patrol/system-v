module SystemV.DSL.Build.Result

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

import        SystemV.Types
import        SystemV.Terms

import        SystemV.DSL.AST
import        SystemV.DSL.Build.Context

import        SystemV.Utilities

%default total

public export
data BuildRes : (lvls : Universes)
             -> (ctxt : Context lvls)
                     -> Type
  where
    Res : {ctxt : Context lvls}
       -> (u    : Universe)
       -> (type : MTy u)
       -> (term : SystemV ctxt type)
               -> BuildRes lvls ctxt


-- --------------------------------------------------------------------- [ EOF ]
