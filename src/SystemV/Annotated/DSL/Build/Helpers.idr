module SystemV.Annotated.DSL.Build.Helpers

import        Decidable.Equality

import        Data.Vect
import        Data.Nat
import        Data.List
import        Data.List.Views
import        Data.String
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem


import public Toolkit.Decidable.Informative
import public Toolkit.Decidable.Equality.Indexed

import        Toolkit.Decidable.Equality.Views

import        SystemV.Common.Utilities

import        SystemV.Common.Builder

import        SystemV.Annotated.Types
import        SystemV.Annotated.Types.Views
import        SystemV.Annotated.Terms

import        SystemV.Annotated.DSL.AST
import public SystemV.Annotated.DSL.Error

%default total

public export
TermBuilder : Type -> Type
TermBuilder = Either Annotated.Error

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

export
isChan : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (i ** s ** ty ** SystemV types (ChanTy ty s i))
isChan fc term with (view (isChan) term)
  isChan fc (Res u type term) | (HasView prf) with (type)
    isChan fc (Res (IDX TERM) type term) | (HasView Match) | (ChanTy ty s i) = Right (i ** s ** ty ** term)
    isChan fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotAChannel type'))

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

public export
data PortVect : {lvls  : Universes}
             -> (types : Context lvls)
             -> Type
  where
    PV : {lvls  : Universes}
      -> {types : Context lvls}
      -> {tyD   : _}
      -> {dir   : _}
      -> {s     : Sensitivity}
      -> {i     : Intention}
      -> (w     : Whole)
      -> (term  : SystemV types (PortTy (VectorTyDesc w tyD) dir s i))
               -> PortVect types

export
isPortVect : {lvls  : Universes}
          -> {types : Context lvls}
          -> FileContext
          -> (port  : Result TYPE SystemV lvls types)
                   -> TermBuilder (PortVect types)
isPortVect fc port with (view (isPortVect) port)
  isPortVect fc (Res u type term) | (HasView prf) with (type)
    isPortVect fc (Res (IDX TERM) type term) | (HasView Match) | (PortTy (VectorTyDesc w ty) dir s i)
      = Right (PV w term)

    isPortVect fc (Res (IDX TERM) type term) | (HasView Fail) | (PortTy ty dir s i)
      = Left (Err fc (WrongType NotAVect (PortTy ty dir s i)))

    isPortVect fc (Res u type term) | (HasView NotAPort) | type'
      = Left (Err fc (WrongType NotAPort type'))

-- @TODO Clean
export
isPortWithDir : {lvls  : Universes}
             -> {types : Context lvls}
             -> FileContext
             -> (port  : Result TYPE SystemV lvls types)
             -> (dir   : Direction)
                      -> TermBuilder (i ** s ** tyD ** SystemV types (PortTy tyD dir s i))
isPortWithDir fc port dir with (view (hasDirection dir) port)
  isPortWithDir fc (Res u type term) dir | (HasView prf) with (type)
    isPortWithDir fc (Res (IDX TERM) type term) db | (HasView (Match Refl)) | (PortTy ty db s i)
      = pure (i ** s ** ty ** term)
    isPortWithDir fc (Res (IDX TERM) type term) dir | (HasView (Fail contra)) | (PortTy ty db s i)
      = Left (Err fc (TypeMismatch (PortTy ty dir s i) (PortTy ty db s i)))
    isPortWithDir fc (Res u type term) dir | (HasView NotAPort) | type'
      = Left (Err fc (WrongType NotAPort type'))

public export
data Port : {lvls  : Universes}
         -> (types : Context lvls)
                   -> Type
  where
    P : {lvls  : Universes}
     -> {types : Context lvls}
     -> (i    : Intention)
     -> (s    : Sensitivity)
     -> (d    : Direction)
     -> (ty   : TYPE (DATA TYPE))
     -> (port : SystemV types (PortTy ty d s i))
              -> Port types

export
isPort : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (port  : Result TYPE SystemV lvls types)
               -> TermBuilder (Port types)
isPort fc port with (view isPort port)
  isPort fc (Res u type term) | (HasView prf) with (type)
    isPort fc (Res (IDX TERM) type term) | (HasView Match) | (PortTy ty dir s i)
      = Right (P i s dir ty term)
    isPort fc (Res u type term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType NotAPort ty'))


-- [ EOF ]
