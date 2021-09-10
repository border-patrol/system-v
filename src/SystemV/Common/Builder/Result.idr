module SystemV.Common.Builder.Result

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.String
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

import        SystemV.Common.Utilities

import        SystemV.Common.Types.Universe

%default total

public export
data Result : (typeDesc : Universe -> Type)
           -> (termDesc : {lvl : Universe} -> {lvls : List Universe} -> DList Universe typeDesc lvls -> typeDesc lvl -> Type)
           -> (lvls : List Universe)
           -> (ctxt : DList Universe typeDesc lvls)
                   -> Type
  where
    Res : {tyDesc : Universe -> Type}
       -> {tmDesc : {lvl : Universe} -> {lvls : List Universe} -> DList Universe tyDesc lvls -> tyDesc lvl -> Type}
       -> {lvls : List Universe}
       -> {ctxt : DList Universe tyDesc lvls}
       -> (u    : Universe)
       -> (type : tyDesc u)
       -> (term : tmDesc ctxt type)
               -> Result tyDesc tmDesc lvls ctxt

public export
data View : (typeDesc : Universe -> Type)
         -> (termDesc : {lvl  : Universe}
                     -> {lvls : List Universe}
                     -> (ctxt : DList Universe typeDesc lvls)
                     -> (type : typeDesc lvl)
                              -> Type)
         -> {lvls : List Universe}
         -> {types : DList Universe typeDesc lvls}
         -> (pred : (v : Universe) -> (type : typeDesc v) -> Type)
         -> (res  : Result typeDesc termDesc lvls types)
                 -> Type
  where
    HasView : {tyDesc : (u : Universe) -> Type}
           -> {tmDesc : {lvl  : Universe}
                     -> {lvls : List Universe}
                     -> (ctxt : DList Universe tyDesc lvls)
                     -> (type : tyDesc lvl)
                             -> Type}
           -> {pred : (v : Universe) -> (type : tyDesc v) -> Type}
           -> {lvls : List Universe}
           -> {ctxt : DList Universe tyDesc lvls}
           -> {u    : Universe}
           -> {type : tyDesc u}
           -> {term : tmDesc ctxt type}
           -> (prf  : pred u type)
                   -> View tyDesc tmDesc pred (Res u type term)

export
view : {tyDesc : Universe -> Type}
    -> {tmDesc : {lvl  : Universe}
              -> {lvls : List Universe}
              -> (ctxt : DList Universe tyDesc lvls)
              -> (type : tyDesc lvl)
                      -> Type}
    -> {pred  : (v : Universe) -> (type : tyDesc v) -> Type}
    -> {lvls  : List Universe}
    -> {types : DList Universe tyDesc lvls}
    -> (calc  : (v : Universe) -> (type : tyDesc v) -> (pred v type))
    -> (res   : Result tyDesc tmDesc lvls types)
            -> View tyDesc tmDesc pred res
view calc (Res u type term) with (calc u type)
  view calc (Res u type term) | (prf) = HasView prf
-- [ EOF ]
