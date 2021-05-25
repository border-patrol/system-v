module SystemV.Common.Builder.Context

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
import        SystemV.Common.Types.Universe

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
  Names : List Universe -> Type
  Names = DList Universe Name

  listEmpty : (level ** Elem Universe Name (MkName (Just name) level) Nil) -> Void
  listEmpty (MkDPair fst snd) impossible


  nameNotInRest : (contraE : HasName name x (MkName s x) -> Void)
               -> (contraR : (level : Universe ** Elem Universe Name (MkName (Just name) level) rest) -> Void)
               -> (prf     : (level : Universe ** Elem Universe Name (MkName (Just name) level) (MkName s x :: rest)) )
                          -> Void
  nameNotInRest contraE contraR (MkDPair x (H (Same Refl Refl))) = contraE (YesHasName Refl)
  nameNotInRest contraE contraR (MkDPair fst (T later)) = contraR (MkDPair fst later)


  export
  isName : (name  : String)
         -> (names : Names lvls)
         -> Dec (level ** Elem Universe Name (MkName (Just name) level) names)
  isName name [] = No listEmpty
  isName name ((MkName s x) :: rest) with (hasName name x (MkName s x))
    isName n ((MkName (Just n) x) :: rest) | (Yes (YesHasName Refl))
      = Yes (MkDPair x (H (Same Refl Refl)))
    isName name ((MkName s x) :: rest) | (No contra) with (isName name rest)
      isName name ((MkName s x) :: rest) | (No contra) | (Yes (MkDPair fst snd))
        = Yes (MkDPair fst (T snd))
      isName name ((MkName s x) :: rest) | (No contra) | (No f)
        = No (nameNotInRest contra f)

export
mkVar : {names : Names lvls}
     -> (prf   : Elem Universe Name (MkName (Just name) level) names)
     -> (ctxt  : DList Universe typeDesc lvls)
     -> (type : typeDesc level ** Elem Universe typeDesc type ctxt)
mkVar (H (Same Refl prfVal)) (elem :: rest) = MkDPair elem (H (Same Refl Refl))
mkVar (T later) (elem :: rest) with (mkVar later rest)
  mkVar (T later) (elem :: rest) | (MkDPair fst snd) = MkDPair fst (T snd)

public export
data Context : (type : Universe -> Type)
            -> (lvls : List Universe)
            -> (ctxt : DList Universe type lvls)
                      -> Type
  where
    Ctxt : (lvls  : List Universe)
        -> (names : Names lvls)
        -> (ctxt  : DList Universe type lvls)
                 -> Context type lvls ctxt

-- [ EOF ]
