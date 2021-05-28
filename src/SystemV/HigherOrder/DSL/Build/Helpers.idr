module SystemV.HigherOrder.DSL.Build.Helpers

import        Decidable.Equality

import        Data.Vect
import        Data.Nat
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem


import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import        Toolkit.Decidable.Equality.Views

import        SystemV.Common.Utilities

import        SystemV.Common.Builder

import        SystemV.HigherOrder.Types

import        SystemV.Core.Types.Views

import        SystemV.HigherOrder.Terms

import        SystemV.HigherOrder.DSL.AST
import public SystemV.HigherOrder.DSL.Error

%default total

public export
TermBuilder : Type -> Type
TermBuilder = Either HigherOrder.Error

public export
data FuncDesc : {lvls  : Universes}
             -> (types : Context lvls)
                      -> Type
  where
    FTy : (a     : TYPE (IDX TYPE))
       -> (b     : TYPE (IDX TYPE))
       -> (term  : SystemV types (FuncTy a b))
                -> FuncDesc types
export
isFuncTy : {lvls  : Universes}
        -> {types : Context lvls}
        -> FileContext
        -> (term  : Result TYPE SystemV lvls types)
                 -> TermBuilder (FuncDesc types)
isFuncTy fc term with (view isFuncTy term)
  isFuncTy fc (Res u type term) | (HasView prf) with (type)
    isFuncTy fc (Res (IDX TYPE) type term) | (HasView Match) | (FuncTy a b)
      = Right (FTy a b term)
    isFuncTy fc (Res (IDX _) type term) | (HasView WrongTm) | ty'
      = Left (Err fc (WrongType NotAType ty'))
    isFuncTy fc (Res u type term) | (HasView NotATerm) | ty'
      = Left (Err fc (WrongType NotAType ty'))


public export
data Func : {lvls  : Universes}
         -> (types : Context lvls)
                  -> Type
  where
    F : (a     : (TYPE (IDX TERM)))
     -> (b     : TYPE (IDX TERM))
     -> (term  : SystemV types (FuncTy a b))
              -> Func types
export
isFunc : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (Func types)
isFunc fc term with (view isFunc term)
  isFunc fc (Res u type term) | (HasView prf) with (type)
    isFunc fc (Res (IDX TERM) type term) | (HasView Match) | (FuncTy a b)
      = Right (F a b term)
    isFunc fc (Res (IDX _) type term) | (HasView WrongTm) | ty'
      = Left (Err fc (WrongType NotAFunc ty'))
    isFunc fc (Res u type term) | (HasView NotATerm) | ty'
      = Left (Err fc (WrongType NotAFunc ty'))

public export
data Data : {lvls  : Universes}
         -> (types : Context lvls)
                  -> Type
  where
    D : (type  : TYPE (DATA TYPE))
     -> (term  : SystemV types type)
              -> Data types
export
isData : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (ctxt  : NotDataTypeContext)
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (Data types)
isData fc ctxt term with (view isData term)
  isData fc ctxt (Res u type term) | (HasView prf) with (type)
    isData fc ctxt (Res (DATA TYPE) type term) | (HasView Match) | ty'
      = Right (D ty' term)
    isData fc ctxt (Res u type term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType (NotADataType ctxt) ty'))

public export
data Term : {lvls  : Universes}
         -> (types : Context lvls)
                  -> Type
  where
    T : {level : Level}
     -> (type  : TYPE (IDX level))
     -> (term  : SystemV types type)
              -> Term types
export
isTerm : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (Term types)
isTerm fc term with (view isTerm term)
  isTerm fc (Res u ty term) | (HasView prf) with (ty)
    isTerm fc (Res (IDX level) ty term) | (HasView Match) | ty'
      = Right (T ty' term)
    isTerm fc (Res u ty term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType NotATerm ty'))

public export
data TermTerm : {lvls  : Universes}
             -> (types : Context lvls)
                      -> Type
  where
    TTerm : (type  : TYPE (IDX TERM))
         -> (term  : SystemV types type)
                  -> TermTerm types

export
isTermTerm : {lvls  : Universes}
          -> {types : Context lvls}
          -> FileContext
          -> (term  : Result TYPE SystemV lvls types)
                   -> TermBuilder (TermTerm types)
isTermTerm fc term with (view isTerm term)
  isTermTerm fc (Res u ty term) | (HasView prf) with (ty)
    isTermTerm fc (Res (IDX TERM) ty term) | (HasView Match) | ty'
      = Right (TTerm ty' term)
    isTermTerm fc (Res (IDX TYPE) ty term) | (HasView Match) | ty'
      = Left (Err fc (WrongType NotATerm ty'))

    --Right (T ty' term)
    isTermTerm fc (Res u ty term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType NotATerm ty'))

public export
data TermT : {lvls  : Universes}
          -> (types : Context lvls)
                   -> Type
  where
    TT : (type  : TYPE (IDX TYPE))
      -> (term  : SystemV types type)
               -> TermT types
export
isType : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (TermT types)
isType fc term with (view isType term)
  isType fc (Res u type term) | (HasView prf) with (type)
    isType fc (Res (IDX TYPE) type term) | (HasView Match) | ty'
      = Right (TT ty' term)
    isType fc (Res u type term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType NotAType ty'))

export
isUnit : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (SystemV types UnitTy)
isUnit fc term with (view (isUnit) term)
  isUnit fc (Res u type term) | (HasView prf) with (type)
    isUnit fc (Res (IDX TERM) type term) | (HasView Match) | UnitTy = Right term
    isUnit fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotAUnit type'))

export
isChan : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (ty ** SystemV types (ChanTy ty))
isChan fc term with (view (isChan) term)
  isChan fc (Res u type term) | (HasView prf) with (type)
    isChan fc (Res (IDX TERM) type term) | (HasView Match) | (ChanTy ty) = Right (ty ** term)
    isChan fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotAChannel type'))

public export
data PortVect : {lvls  : Universes}
             -> (types : Context lvls)
             -> Type
  where
    PV : {lvls  : Universes}
      -> {types : Context lvls}
      -> {tyD   : _}
      -> {dir   : _}
      -> (s     : Whole)
      -> (term  : SystemV types (PortTy (VectorTyDesc s tyD) dir))
               -> PortVect types

export
isPortVect : {lvls  : Universes}
          -> {types : Context lvls}
          -> FileContext
          -> (port  : Result TYPE SystemV lvls types)
                   -> TermBuilder (PortVect types)
isPortVect fc port with (view (isPortVect) port)
  isPortVect fc (Res u type term) | (HasView prf) with (type)
    isPortVect fc (Res (IDX TERM) type term) | (HasView Match) | (PortTy (VectorTyDesc s ty) dir)
      = Right (PV s term)
    isPortVect fc (Res (IDX TERM) type term) | (HasView Fail) | (PortTy ty dir)
      = Left (Err fc (WrongType NotAVect (PortTy ty dir)))
    isPortVect fc (Res u type term) | (HasView NotAPort) | type'
      = Left (Err fc (WrongType NotAPort type'))

-- @TODO Clean
export
isPortWithDir : {lvls  : Universes}
             -> {types : Context lvls}
             -> FileContext
             -> (port  : Result TYPE SystemV lvls types)
             -> (dir   : Direction)
                      -> TermBuilder (tyD ** SystemV types (PortTy tyD dir))
isPortWithDir fc port dir with (view (hasDirection dir) port)
  isPortWithDir fc (Res u type term) dir | (HasView prf) with (type)
    isPortWithDir fc (Res (IDX TERM) type term) db | (HasView (Match Refl)) | (PortTy ty db)
      = pure (ty ** term)
    isPortWithDir fc (Res (IDX TERM) type term) dir | (HasView (Fail contra)) | (PortTy ty db)
      = Left (Err fc (TypeMismatch (PortTy ty dir) (PortTy ty db)))
    isPortWithDir fc (Res u type term) dir | (HasView NotAPort) | type'
      = Left (Err fc (WrongType NotAPort type'))

public export
data Port : {lvls  : Universes}
         -> (types : Context lvls)
                   -> Type
  where
    P : {lvls  : Universes}
     -> {types : Context lvls}
     -> (d    : Direction)
     -> (ty   : TYPE (DATA TYPE))
     -> (port : SystemV types (PortTy ty d))
              -> Port types

export
isPort : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (port  : Result TYPE SystemV lvls types)
               -> TermBuilder (Port types)
isPort fc port with (view isPort port)
  isPort fc (Res u type term) | (HasView prf) with (type)
    isPort fc (Res (IDX TERM) type term) | (HasView Match) | (PortTy ty dir)
      = Right (P dir ty term)
    isPort fc (Res u type term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType NotAPort ty'))

-- [ EOF ]
