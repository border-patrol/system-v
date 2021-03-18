module SystemV.Arithmetic.DSL.Build.Result

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

import        SystemV.Utilities
import        SystemV.Types

import        SystemV.Arithmetic.Terms
import        SystemV.Arithmetic.DSL.AST
import        SystemV.Arithmetic.DSL.Build.Context


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
