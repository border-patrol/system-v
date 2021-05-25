module SystemV.Core.DSL.Build.Helpers

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

import        SystemV.Core.Types
import        SystemV.Core.Types.Views
import        SystemV.Core.Terms

import        SystemV.Core.DSL.AST
import public SystemV.Core.DSL.Error

%default total

public export
TermBuilder : Type -> Type
TermBuilder = Either Core.Error

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
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (Func types)
isFunc term with (view isFunc term)
  isFunc (Res u type term) | (HasView prf) with (type)
    isFunc (Res (IDX TERM) type term) | (HasView Match) | (FuncTy a b)
      = Right (F a b term)
    isFunc (Res (IDX _) type term) | (HasView WrongTm) | ty'
      = Left (WrongType NotAFunc ty')
    isFunc (Res u type term) | (HasView NotATerm) | ty'
      = Left (WrongType NotAFunc ty')

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
      -> (ctxt  : NotDataTypeContext)
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (Data types)
isData ctxt term with (view isData term)
  isData ctxt (Res u type term) | (HasView prf) with (type)
    isData ctxt (Res (DATA TYPE) type term) | (HasView Match) | ty'
      = Right (D ty' term)
    isData ctxt (Res u type term) | (HasView Fail) | ty'
      = Left (WrongType (NotADataType ctxt) ty')

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
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (Term types)
isTerm term with (view isTerm term)
  isTerm (Res u ty term) | (HasView prf) with (ty)
    isTerm (Res (IDX level) ty term) | (HasView Match) | ty'
      = Right (T ty' term)
    isTerm (Res u ty term) | (HasView Fail) | ty'
      = Left (WrongType NotATerm ty')

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
          -> (term  : Result TYPE SystemV lvls types)
                   -> TermBuilder (TermTerm types)
isTermTerm term with (view isTerm term)
  isTermTerm (Res u ty term) | (HasView prf) with (ty)
    isTermTerm (Res (IDX TERM) ty term) | (HasView Match) | ty'
      = Right (TTerm ty' term)
    isTermTerm (Res (IDX TYPE) ty term) | (HasView Match) | ty'
      = Left (WrongType NotATerm ty')

    --Right (T ty' term)
    isTermTerm (Res u ty term) | (HasView Fail) | ty'
      = Left (WrongType NotATerm ty')

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
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (TermT types)
isType term with (view isType term)
  isType (Res u type term) | (HasView prf) with (type)
    isType (Res (IDX TYPE) type term) | (HasView Match) | ty'
      = Right (TT ty' term)
    isType (Res u type term) | (HasView Fail) | ty'
      = Left (WrongType NotAType ty')

export
isUnit : {lvls  : Universes}
      -> {types : Context lvls}
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (SystemV types UnitTy)
isUnit term with (view (isUnit) term)
  isUnit (Res u type term) | (HasView prf) with (type)
    isUnit (Res (IDX TERM) type term) | (HasView Match) | UnitTy = Right term
    isUnit (Res u type term) | (HasView Fail) | type'
      = Left (WrongType NotAUnit type')

export
isChan : {lvls  : Universes}
      -> {types : Context lvls}
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (ty ** SystemV types (ChanTy ty))
isChan term with (view (isChan) term)
  isChan (Res u type term) | (HasView prf) with (type)
    isChan (Res (IDX TERM) type term) | (HasView Match) | (ChanTy ty) = Right (ty ** term)
    isChan (Res u type term) | (HasView Fail) | type'
      = Left (WrongType NotAChannel type')

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
          -> (port  : Result TYPE SystemV lvls types)
                   -> TermBuilder (PortVect types)
isPortVect port with (view (isPortVect) port)
  isPortVect (Res u type term) | (HasView prf) with (type)
    isPortVect (Res (IDX TERM) type term) | (HasView Match) | (PortTy (VectorTyDesc s ty) dir)
      = Right (PV s term)
    isPortVect (Res (IDX TERM) type term) | (HasView Fail) | (PortTy ty dir)
      = Left (WrongType NotAVect (PortTy ty dir))
    isPortVect (Res u type term) | (HasView NotAPort) | type'
      = Left (WrongType NotAPort type')

-- @TODO Clean
export
isPortWithDir : {lvls  : Universes}
             -> {types : Context lvls}
             -> (port  : Result TYPE SystemV lvls types)
             -> (dir   : Direction)
                      -> TermBuilder (tyD ** SystemV types (PortTy tyD dir))
isPortWithDir port dir with (view (hasDirection dir) port)
  isPortWithDir (Res u type term) dir | (HasView prf) with (type)
    isPortWithDir (Res (IDX TERM) type term) db | (HasView (Match Refl)) | (PortTy ty db)
      = pure (ty ** term)
    isPortWithDir (Res (IDX TERM) type term) dir | (HasView (Fail contra)) | (PortTy ty db)
      = Left (TypeMismatch (PortTy ty dir) (PortTy ty db))
    isPortWithDir (Res u type term) dir | (HasView NotAPort) | type'
      = Left (WrongType NotAPort type')

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
      -> (port  : Result TYPE SystemV lvls types)
               -> TermBuilder (Port types)
isPort port with (view isPort port)
  isPort (Res u type term) | (HasView prf) with (type)
    isPort (Res (IDX TERM) type term) | (HasView Match) | (PortTy ty dir)
      = Right (P dir ty term)
    isPort (Res u type term) | (HasView Fail) | ty'
      = Left (WrongType NotAPort ty')


public export
data NotPorts : {lvls    : Universes}
             -> (types   : Context lvls)
                        -> Type
  where
    NP : {ty : _}
      -> (pout : SystemV types (PortTy ty OUT))
      -> (pin  : SystemV types (PortTy ty IN))
              -> NotPorts types

export
notGatePorts : {lvls  : Universes}
            -> {types : Context lvls}
            -> (portOUT : Result TYPE SystemV lvls types)
            -> (portIN  : Result TYPE SystemV lvls types)
                       -> TermBuilder (NotPorts types)
notGatePorts portOUT portIN
  = do (to ** output) <- isPortWithDir portOUT OUT
       (ti ** input)  <- isPortWithDir portIN  IN

       let po = PortTy to OUT
       let pi = PortTy ti IN

       case DataTypes.decEq to ti of
         Yes (Same Refl Refl) =>
           Right (NP output input)

         No msgWhyNot prfWhyNot =>
           Left (TypeMismatch to ti)

public export
data Conditionals : {lvls    : Universes}
                 -> (types   : Context lvls)
                            -> Type
  where
    IF : {ty : _}
      -> (cond : SystemV types (PortTy ty IN))
      -> (tt   : SystemV types UnitTy)
      -> (ff   : SystemV types UnitTy)
              -> Conditionals types

export
conditionals : {lvls  : Universes}
            -> {types : Context lvls}
            -> (cond  : Result TYPE SystemV lvls types)
            -> (tt    : Result TYPE SystemV lvls types)
            -> (ff    : Result TYPE SystemV lvls types)
                     -> TermBuilder (Conditionals types)
conditionals cond tt ff
  = do (tyD ** cc) <- isPortWithDir cond IN
       t  <- isUnit tt
       f  <- isUnit ff
       pure (IF cc t f)


public export
data BinPorts : {lvls    : Universes}
             -> (types   : Context lvls)
                        -> Type
  where
    BP : {ty   : _}
      -> (pout : SystemV types (PortTy ty OUT))
      -> (pinA : SystemV types (PortTy ty IN))
      -> (pinB : SystemV types (PortTy ty IN))
              -> BinPorts types

export
binGatePorts : {lvls    : Universes}
            -> {types   : Context lvls}
            -> (portOUT : Result TYPE SystemV lvls types)
            -> (portInA : Result TYPE SystemV lvls types)
            -> (portInB : Result TYPE SystemV lvls types)
                       -> TermBuilder (BinPorts types)
binGatePorts o a b
  = do (to ** output) <- isPortWithDir o OUT
       (ta ** inputA) <- isPortWithDir a IN
       (tb ** inputB) <- isPortWithDir b IN

       let po = PortTy to OUT
       let pa = PortTy ta IN
       let pb = PortTy tb IN

       case allDataEqual to ta tb of
         No AB contra => Left (TypeMismatch to ta)
         No AC contra => Left (TypeMismatch to tb)
         Yes ADE      => Right (BP output inputA inputB)

export
canCast : {lvls  : Universes}
       -> {types : Context lvls}
       -> (port  : Result TYPE SystemV lvls types)
       -> (toTy  : Result TYPE SystemV lvls types)
       -> (toDir : Direction)
                -> TermBuilder (Result TYPE SystemV lvls types)
canCast port toTy toDir
  = do (P fromDir fromTy from) <- isPort port
       (D toDTy data_) <- isData InCast toTy

       let fromP = PortTy fromTy fromDir
       let toP   = PortTy toDTy   toDir

       case validCast (PortTy fromTy fromDir) (PortTy toDTy toDir) of
         (Yes prfWhy)             => Right (Res _ _ (Cast from prfWhy))
         (No msgWhyNot prfWhyNot) => Left (InvalidCast msgWhyNot fromP toP)

public export
data ConnectPorts : {lvls    : Universes}
                 -> (types   : Context lvls)
                            -> Type
  where
    CP : {ty  : _}
      -> {dirA,dirB : Direction}
      -> (pA  : SystemV types (PortTy ty dirA))
      -> (pB  : SystemV types (PortTy ty dirB))
      -> (prf : ValidFlow dirA dirB)
             -> ConnectPorts types
export
connectPorts : {lvls  : Universes}
            -> {types : Context lvls}
            -> (a     : Result TYPE SystemV lvls types)
            -> (b     : Result TYPE SystemV lvls types)
                     -> TermBuilder (ConnectPorts types)
connectPorts a b
  = do (P da ta pa) <- isPort a
       (P db tb pb) <- isPort b

       let ptA = PortTy ta da
       let ptB = PortTy tb db

       case DataTypes.decEq ta tb of
         (Yes (Same Refl Refl)) =>
           case validFlow da db of
             (Yes x) => Right (CP pa pb x)

             (No msgWhyNot prfWhyNot) =>
               Left (InvalidFlow msgWhyNot)
         (No msgWhyNot prfWhyNot) =>
           Left (TypeMismatch ptA ptB)

public export
data Application: {lvls    : Universes}
               -> (types   : Context lvls)
                          -> Type
  where
    APP : {a : TYPE (IDX TERM)}
       -> {b : _}
       -> (func  : SystemV types (FuncTy a b))
       -> (param : SystemV types a)
                -> Application types

export
application : {lvls  : Universes}
           -> {types : Context lvls}
           -> (a     : Result TYPE SystemV lvls types)
           -> (b     : Result TYPE SystemV lvls types)
                    -> TermBuilder (Application types)
application fun arg
  = do (F     tyA  tyB f) <- isFunc     fun
       (TTerm tyA'     a) <- isTermTerm arg
       case TypeTerms.decEq tyA tyA' of
         (Yes (Same Refl Refl)) =>
           Right (APP f a)
         (No msgWhyNot prfWhyNot) =>
           Left (TypeMismatch tyA tyA')


public export
data Annotation : {lvls    : Universes}
               -> (types   : Context lvls)
                          -> Type
  where
    ANN : (meta   : TYPE (IDX TYPE))
       -> (termTy : SystemV types meta)
       -> (termPa : TYPE (IDX TERM))
       -> (chk    : TyCheck meta termPa)
                 -> Annotation types

export
annotation : {lvls  : Universes}
          -> {types : Context lvls}
          -> (type  : Result TYPE SystemV lvls types)
                    -> TermBuilder (Annotation types)
annotation type
  = do (TT ty term) <- isType type
       case synthesis ty of
         Yes (MkDPair argty (Synth argty prfarg prfret chk)) => Right (ANN ty term argty chk)
         No msgWhyNot prfWhyNot => Left (InvalidFuncSynth msgWhyNot ty)

public export
data Body : {lvls    : Universes}
         -> (types   : Context lvls)
         -> (type    : TYPE (IDX TERM))
                    -> Type
  where
    B : {b    : TYPE (IDX TERM)}
     -> (body : SystemV types b)
     -> (chk  : Function.ValidTerm (IDX TERM) (FuncTy a b))
             -> Body types a

export
body : {lvls  : Universes}
    -> {types : Context lvls}
    -> (a     : (TYPE (IDX TERM)))
    -> (type  : Result TYPE SystemV lvls types)
              -> TermBuilder (Body types a)
body a type
  = do (TTerm ty term) <- isTermTerm type
       case Function.validTerm (IDX TERM) (FuncTy a ty) of
         Yes prfWhy => Right (B term prfWhy)
         No msgWhyNot prfWhyNot => (Left (InvalidFunc msgWhyNot a ty))




-- [ EOF ]
