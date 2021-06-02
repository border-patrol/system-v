module SystemV.Params.DSL.Build.Helpers

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

import        SystemV.Params.Types
import        SystemV.Params.Types.TYPE.Equality.DataTerms
import        SystemV.Params.Types.Views
import        SystemV.Params.Terms

import        SystemV.Params.DSL.AST
import public SystemV.Params.DSL.Error

%default total

public export
TermBuilder : Type -> Type
TermBuilder = Either Params.Error

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

export
isData : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (ctxt  : NotDataTypeContext)
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (SystemV types DATATERM)
isData fc ctxt term with (view isData term)
  isData fc ctxt (Res u type term) | (HasView prf) with (type)
    isData fc ctxt (Res (DATA TERM) type term) | (HasView Match) | DATATERM
      = Right term
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
               -> TermBuilder (SystemV types (ChanTy))
isChan fc term with (view (isChan) term)
  isChan fc (Res u type term) | (HasView prf) with (type)
    isChan fc (Res (IDX TERM) type term) | (HasView Match) | (ChanTy) = Right (term)
    isChan fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotAChannel type'))

-- @TODO Clean
export
isPortWithDir : {lvls  : Universes}
             -> {types : Context lvls}
             -> FileContext
             -> (port  : Result TYPE SystemV lvls types)
             -> (dir   : Direction)
                      -> TermBuilder (SystemV types (PortTy dir))
isPortWithDir fc port dir with (view (hasDirection dir) port)
  isPortWithDir fc (Res u type term) dir | (HasView prf) with (type)
    isPortWithDir fc (Res (IDX TERM) type term) db | (HasView (Match Refl)) | (PortTy db)
      = pure (term)
    isPortWithDir fc (Res (IDX TERM) type term) dir | (HasView (Fail contra)) | (PortTy db)
      = Left (Err fc (TypeMismatch (PortTy dir) (PortTy db)))
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
     -> (port : SystemV types (PortTy d))
              -> Port types

export
isPort : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (port  : Result TYPE SystemV lvls types)
               -> TermBuilder (Port types)
isPort fc port with (view isPort port)
  isPort fc (Res u type term) | (HasView prf) with (type)
    isPort fc (Res (IDX TERM) type term) | (HasView Match) | (PortTy dir)
      = Right (P dir term)
    isPort fc (Res u type term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType NotAPort ty'))

export
isBool : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (SystemV types BoolTy)
isBool fc term with (view (isBool) term)
  isBool fc (Res u type term) | (HasView prf) with (type)
    isBool fc (Res (IDX TERM) type term) | (HasView Match) | BoolTy = Right term
    isBool fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotABool type'))

export
isNatTy : {lvls  : Universes}
     -> {types : Context lvls}
     -> FileContext
     -> (term  : Result TYPE SystemV lvls types)
              -> TermBuilder (SystemV types NatTyDesc)
isNatTy fc term with (view (isNatTy) term)
  isNatTy fc (Res u type term) | (HasView prf) with (type)
    isNatTy fc (Res (IDX TYPE) type term) | (HasView Match) | NatTyDesc = Right term
    isNatTy fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotANat type'))

export
isNat : {lvls  : Universes}
     -> {types : Context lvls}
     -> FileContext
     -> (term  : Result TYPE SystemV lvls types)
              -> TermBuilder (SystemV types NatTy)
isNat fc term with (view (isNat) term)
  isNat fc (Res u type term) | (HasView prf) with (type)
    isNat fc (Res (IDX TERM) type term) | (HasView Match) | NatTy = Right term
    isNat fc (Res u type term) | (HasView Fail) | type'
      = Left (Err fc (WrongType NotANat type'))


public export
data FuncDef : {lvls  : Universes}
         -> (types : Context lvls)
                  -> Type
  where
    FDef : (u     : Universe)
        -> (a     : (TYPE u))
        -> (b     : TYPE (IDX TERM))
        -> (term  : SystemV types (FuncParamTy u a b))
                 -> FuncDef types
export
isFuncDef : {lvls  : Universes}
      -> {types : Context lvls}
      -> FileContext
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (FuncDef types)
isFuncDef fc term with (view isFuncParam term)
  isFuncDef fc (Res u type term) | (HasView prf) with (type)
    isFuncDef fc (Res (IDX TERM) type term) | (HasView Match) | (FuncParamTy u a b)
      = Right (FDef u a b term)
    isFuncDef fc (Res (IDX _) type term) | (HasView WrongTm) | ty'
      = Left (Err fc (WrongType NotAFuncDef ty'))
    isFuncDef fc (Res u type term) | (HasView NotATerm) | ty'
      = Left (Err fc (WrongType NotAFuncDef ty'))

export
isDataTy : {lvls  : Universes}
        -> {types : Context lvls}
        -> FileContext
        -> (ctxt  : NotDataTypeContext)
        -> (term  : Result TYPE SystemV lvls types)
                 -> TermBuilder (SystemV types DATATYPE)
isDataTy fc ctxt term with (view isDataType term)
  isDataTy fc ctxt (Res u type term) | (HasView prf) with (type)
    isDataTy fc ctxt (Res (DATA TYPE) type term) | (HasView Match) | DATATYPE
      = Right term
    isDataTy fc ctxt (Res u type term) | (HasView Fail) | ty'
      = Left (Err fc (WrongType (NotADataType ctxt) ty'))

-- [ EOF ]
