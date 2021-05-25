module SystemV.Annotated.DSL.Build.Helpers

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

export
isChan : {lvls  : Universes}
      -> {types : Context lvls}
      -> (term  : Result TYPE SystemV lvls types)
               -> TermBuilder (i ** s ** ty ** SystemV types (ChanTy ty s i))
isChan term with (view (isChan) term)
  isChan (Res u type term) | (HasView prf) with (type)
    isChan (Res (IDX TERM) type term) | (HasView Match) | (ChanTy ty s i) = Right (i ** s ** ty ** term)
    isChan (Res u type term) | (HasView Fail) | type'
      = Left (WrongType NotAChannel type')

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
          -> (port  : Result TYPE SystemV lvls types)
                   -> TermBuilder (PortVect types)
isPortVect port with (view (isPortVect) port)
  isPortVect (Res u type term) | (HasView prf) with (type)
    isPortVect (Res (IDX TERM) type term) | (HasView Match) | (PortTy (VectorTyDesc w ty) dir s i)
      = Right (PV w term)
    isPortVect (Res (IDX TERM) type term) | (HasView Fail) | (PortTy ty dir s i)
      = Left (WrongType NotAVect (PortTy ty dir s i))
    isPortVect (Res u type term) | (HasView NotAPort) | type'
      = Left (WrongType NotAPort type')

-- @TODO Clean
export
isPortWithDir : {lvls  : Universes}
             -> {types : Context lvls}
             -> (port  : Result TYPE SystemV lvls types)
             -> (dir   : Direction)
                      -> TermBuilder (i ** s ** tyD ** SystemV types (PortTy tyD dir s i))
isPortWithDir port dir with (view (hasDirection dir) port)
  isPortWithDir (Res u type term) dir | (HasView prf) with (type)
    isPortWithDir (Res (IDX TERM) type term) db | (HasView (Match Refl)) | (PortTy ty db s i)
      = pure (i ** s ** ty ** term)
    isPortWithDir (Res (IDX TERM) type term) dir | (HasView (Fail contra)) | (PortTy ty db s i)
      = Left (TypeMismatch (PortTy ty dir s i) (PortTy ty db s i))
    isPortWithDir (Res u type term) dir | (HasView NotAPort) | type'
      = Left (WrongType NotAPort type')

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
      -> (port  : Result TYPE SystemV lvls types)
               -> TermBuilder (Port types)
isPort port with (view isPort port)
  isPort (Res u type term) | (HasView prf) with (type)
    isPort (Res (IDX TERM) type term) | (HasView Match) | (PortTy ty dir s i)
      = Right (P i s dir ty term)
    isPort (Res u type term) | (HasView Fail) | ty'
      = Left (WrongType NotAPort ty')

public export
data PortAttr : {lvls  : Universes}
             -> (types : Context lvls)
             -> (i : Intention)
             -> (s : Sensitivity)
             -> (d : Direction)
                      -> Type
  where
    Pa : {lvls  : Universes}
      -> {types : Context lvls}
      -> (ty   : TYPE (DATA TYPE))
      -> (port : SystemV types (PortTy ty d s i))
              -> PortAttr types i s d

export
isPortAttr : {lvls  : Universes}
          -> {types : Context lvls}
          -> (port  : Result TYPE SystemV lvls types)
          -> (d     : Direction)
          -> (s     : Sensitivity)
          -> (i     : Intention)
                   -> TermBuilder (PortAttr types i s d)
isPortAttr port d s i
  = do (P ip sp dp ty p) <- isPort port
       let pg = PortTy ty dp sp ip
       let pe = PortTy ty d  s  i
       case decEq ip i of
         Yes Refl =>
           case decEq sp s of
             Yes Refl =>
               case Direction.decEq dp d of
                 Yes Refl => Right (Pa ty p)
                 No contra => Left (TypeMismatch pe pg)
             No contra =>
               Left (TypeMismatch pe pg)
         No contra =>
           Left (TypeMismatch pe pg)

public export
data NotPorts : {lvls    : Universes}
             -> (types   : Context lvls)
                        -> Type
  where
    NP : {ty : _}
      -> {s     : Sensitivity}
      -> {i     : Intention}
      -> (pout : SystemV types (PortTy ty OUT s i))
      -> (pin  : SystemV types (PortTy ty IN  s i))
              -> NotPorts types

export
notGatePorts : {lvls  : Universes}
            -> {types : Context lvls}
            -> (portOUT : Result TYPE SystemV lvls types)
            -> (portIN  : Result TYPE SystemV lvls types)
                       -> TermBuilder (NotPorts types)
notGatePorts portOUT portIN
  = do (io ** so ** to ** output) <- isPortWithDir portOUT OUT
       (ii ** si ** ti ** input)  <- isPortWithDir portIN  IN

       let po = PortTy to OUT so io
       let pi = PortTy ti IN  si ii

       case DataTypes.decEq to ti of
         Yes (Same Refl Refl) =>
           case decEq so si of
             Yes Refl =>
               case decEq io ii of
                 Yes Refl => Right (NP output input)
                 No contra =>
                   Left (TypeMismatch po pi)
             No contra =>
                 Left (TypeMismatch po pi)
         No msgWhyNot prfWhyNot =>
           Left (TypeMismatch po pi)

public export
data Conditionals : {lvls    : Universes}
                 -> (types   : Context lvls)
                            -> Type
  where
    IF : {ty : _}
      -> {s  : Sensitivity}
      -> {i  : Intention}
      -> (cond : SystemV types (PortTy ty IN s i))
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
  = do (i ** s ** tyD ** cc) <- isPortWithDir cond IN
       t  <- isUnit tt
       f  <- isUnit ff
       pure (IF cc t f)


public export
data BinPorts : {lvls    : Universes}
             -> (types   : Context lvls)
                        -> Type
  where
    BP : {ty   : _}
      -> {s  : Sensitivity}
      -> {i  : Intention}
      -> (pout : SystemV types (PortTy ty OUT s i))
      -> (pinA : SystemV types (PortTy ty IN  s i))
      -> (pinB : SystemV types (PortTy ty IN  s i))
              -> BinPorts types

export
binGatePorts : {lvls    : Universes}
            -> {types   : Context lvls}
            -> (portOUT : Result TYPE SystemV lvls types)
            -> (portInA : Result TYPE SystemV lvls types)
            -> (portInB : Result TYPE SystemV lvls types)
                       -> TermBuilder (BinPorts types)
binGatePorts o a b
  = do (io ** so ** to ** output) <- isPortWithDir o OUT
       (ia ** sa ** ta ** inputA) <- isPortWithDir a IN
       (ib ** sb ** tb ** inputB) <- isPortWithDir b IN

       let po = PortTy to OUT so io
       let pa = PortTy ta IN sa ia
       let pb = PortTy tb IN sb ib

       case allDataEqual to ta tb of
         No AB contra => Left (TypeMismatch po pa)
         No AC contra => Left (TypeMismatch po pb)
         Yes ADE =>
           case allEqual so sa sb of
             No AB prfWhyNot => Left (TypeMismatch po pa)
             No AC prfWhyNot => Left (TypeMismatch po pb)
             Yes AE =>
               case allEqual io ia ib of
                 No AB prfWhyNot => Left (TypeMismatch po pa)
                 No AC prfWhyNot => Left (TypeMismatch po pb)
                 Yes AE => Right (BP output inputA inputB)

export
canCast : {lvls  : Universes}
       -> {types : Context lvls}
       -> (port  : Result TYPE SystemV lvls types)
       -> (toTy  : Result TYPE SystemV lvls types)
       -> (toDir : Direction)
       -> (s     : Sensitivity)
       -> (i     : Intention)
                -> TermBuilder (Result TYPE SystemV lvls types)
canCast port toTy toDir toS toI

  = do (P fromI fromS fromDir fromTy from) <- isPort port
       (D toDTy data_) <- isData InCast toTy

       let fromP = PortTy fromTy fromDir fromS fromI
       let toP   = PortTy toDTy  toDir   toS   toI

       case cast (PortTy fromTy fromDir fromS fromI) (PortTy toDTy toDir toS toI) of
         (Yes prfWhy)             => Right (Res _ _ (Cast from prfWhy))
         (No msgWhyNot prfWhyNot) => Left (InvalidCast msgWhyNot fromP toP)

public export
data ConnectPorts : {lvls    : Universes}
                 -> (types   : Context lvls)
                            -> Type
  where
    CP : {ty  : _}
      -> {dirA,dirB : Direction}
      -> {s     : Sensitivity}
      -> {i     : Intention}
      -> (pA  : SystemV types (PortTy ty dirA s i))
      -> (pB  : SystemV types (PortTy ty dirB s i))
      -> (prf : ValidFlow dirA dirB)
             -> ConnectPorts types
export
connectPorts : {lvls  : Universes}
            -> {types : Context lvls}
            -> (a     : Result TYPE SystemV lvls types)
            -> (b     : Result TYPE SystemV lvls types)
                     -> TermBuilder (ConnectPorts types)
connectPorts a b
  = do (P ia sa da ta pa) <- isPort a
       (P ib sb db tb pb) <- isPort b

       let ptA = PortTy ta da sa ia
       let ptB = PortTy tb db sb ib

       case DataTypes.decEq ta tb of
         (Yes (Same Refl Refl)) =>
           case decEq sa sb of
             Yes Refl =>
               case decEq ia ib of
                 Yes Refl =>
                   case validFlow da db of
                     Yes prfFlow => Right (CP pa pb prfFlow)
                     No msgWhyNot prfWhyNot =>
                       Left (InvalidFlow msgWhyNot)
                 No contra =>
                  Left (TypeMismatch ptA ptB)

             No contra =>
               Left (TypeMismatch ptA ptB)

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
