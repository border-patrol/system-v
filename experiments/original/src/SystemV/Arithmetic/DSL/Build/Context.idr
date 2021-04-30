module SystemV.Arithmetic.DSL.Build.Context

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


%default total

namespace Name
  public export
  data Name : (u : Universe) -> Type where
    MkName : (s : Maybe String) -> (lvl : Universe) -> Name lvl

  public export
  data HasName : (s : String) -> (lvl : Universe) -> (thing : Name lvl) -> Type where
    YesHasName : (s === x) -> HasName s lvl (MkName (Just x) lvl)

  noname : HasName s lvl (MkName Nothing lvl) -> Void
  noname (YesHasName _) impossible

  wrongName : (contra : s === x -> Void)
           -> (prf    : HasName s lvl (MkName (Just x) lvl))
                     -> Void
  wrongName contra (YesHasName Refl) = contra Refl

  export
  hasName : (s : String) -> (lvl : Universe) -> (thing : Name lvl) -> Dec (HasName s lvl thing)
  hasName s lvl (MkName Nothing lvl) = No noname
  hasName s lvl (MkName (Just x) lvl) with (decEq s x)
    hasName s lvl (MkName (Just x) lvl) | (Yes prf) = Yes (YesHasName prf)
    hasName s lvl (MkName (Just x) lvl) | (No contra) = No (wrongName contra)

  public export
  Names : Universes -> Type
  Names = DList Universe Name

  listEmpty : (level ** Elem Universe Name (MkName (Just name) level) Nil) -> Void
  listEmpty (MkDPair _ (H x)) impossible
  listEmpty (MkDPair _ (T later)) impossible

  notInLater : (contra : (level ** Elem Universe Name (MkName (Just name) level) xs) -> Void)
            -> (prf    : (level ** Elem Universe Name (MkName (Just name) level) (MkName Nothing level'::xs)))
                      -> Void
  notInLater _ (MkDPair _ (H (Same Refl Refl))) impossible
  notInLater contra (MkDPair fst (T later)) = contra (MkDPair fst later)

  nameNotInRest : (contraE : HasName name x (MkName (Just y) x) -> Void)
               -> (contraR : (level : Universe ** Elem Universe Name (MkName (Just name) level) rest) -> Void)
               -> (prf     : (level : Universe ** Elem Universe Name (MkName (Just name) level) (MkName (Just y) x :: rest)) )
                          -> Void
  nameNotInRest contraE contraR (MkDPair x (H (Same Refl Refl))) = contraE (YesHasName Refl)
  nameNotInRest contraE contraR (MkDPair fst (T later)) = contraR (MkDPair fst later)


  export
  isName : (name  : String)
         -> (names : Names lvls)
         -> Dec (level ** Elem Universe Name (MkName (Just name) level) names)
  isName name [] = No listEmpty
  isName name ((MkName Nothing x) :: rest) with (isName name rest)
    isName name ((MkName Nothing x) :: rest) | (Yes (MkDPair fst snd)) = Yes (MkDPair fst (T snd))
    isName name ((MkName Nothing x) :: rest) | (No contra) = No (notInLater contra)
  isName name ((MkName (Just y) x) :: rest) with (hasName name x (MkName (Just y) x))
    isName y ((MkName (Just y) x) :: rest) | (Yes (YesHasName Refl)) = Yes (MkDPair x (H (Same Refl Refl)))
    isName name ((MkName (Just y) x) :: rest) | (No contra) with (isName name rest)
      isName name ((MkName (Just y) x) :: rest) | (No contra) | (Yes (MkDPair fst snd)) = Yes (MkDPair fst (T snd))
      isName name ((MkName (Just y) x) :: rest) | (No contra) | (No f) = No (nameNotInRest contra f)

export
buildVar : {names : Names lvls}
        -> (prf   : Elem Universe Name (MkName (Just name) level) names)
        -> (ctxt  : Context lvls)
        -> (type : Meta level ** Elem Universe Meta type ctxt)
buildVar (H (Same Refl prfVal)) (elem :: rest) = MkDPair elem (H (Same Refl Refl))
buildVar (T later) (elem :: rest) with (buildVar later rest)
  buildVar (T later) (elem :: rest) | (MkDPair fst snd) = MkDPair fst (T snd)

public export
data BuildCtxt : (lvls : Universes)
              -> (ctxt : Context lvls)
                      -> Type
  where
    Ctxt : (lvls : Universes)
        -> (names : Names lvls)
        -> (ctxt : Context lvls)
                -> BuildCtxt lvls ctxt


-- --------------------------------------------------------------------- [ EOF ]
