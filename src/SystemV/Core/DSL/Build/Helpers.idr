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
TermBuilder = Either Build.Error

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
notGatePorts portOUT portIN with (isPortWithDir portOUT OUT)
  notGatePorts portOUT portIN | (Left err)
    = Left err
  notGatePorts portOUT portIN | (Right (MkDPair ty pout)) with (isPortWithDir portIN IN)
    notGatePorts portOUT portIN | (Right (MkDPair ty pout)) | (Left err)
      = Left err
    notGatePorts portOUT portIN | (Right (MkDPair ty pout)) | (Right (MkDPair tyA pin)) with (DataTypes.decEq ty tyA)
      notGatePorts portOUT portIN | (Right (MkDPair ty pout)) | (Right (MkDPair tyA pin)) | (Yes prfWhy) with (prfWhy)
        notGatePorts portOUT portIN | (Right (MkDPair ty pout)) | (Right (MkDPair ty pin)) | (Yes prfWhy) | (Same Refl Refl)
          = Right (NP pout pin)

      notGatePorts portOUT portIN | (Right (MkDPair ty pout)) | (Right (MkDPair tyA pin)) | (No msgWhyNot prfWhyNot)
        = Left (TypeMismatch ty tyA)

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

mkBin : {lvls  : Universes}
     -> {types : Context lvls}
     -> {tyO,tyA,tyB : _}
     -> (pout  : SystemV types (PortTy tyO OUT))
     -> (pinA  : SystemV types (PortTy tyA IN))
     -> (pinB  : SystemV types (PortTy tyB IN))
     -> (prfOA : Equals Universe TYPE tyO tyA)
     -> (prfAB : Equals Universe TYPE tyA tyB)
              -> BinPorts types
mkBin {tyO} {tyA} {tyB} pout pinA pinB prfOA prfAB with (trans prfOA prfAB)
  mkBin {tyO = tyB} {tyA = tyB} {tyB = tyB} pout pinA pinB (Same Refl Refl) (Same Refl Refl) | (Same Refl Refl) = BP pout pinA pinB

export
binGatePorts : {lvls    : Universes}
            -> {types   : Context lvls}
            -> (portOUT : Result TYPE SystemV lvls types)
            -> (portInA : Result TYPE SystemV lvls types)
            -> (portInB : Result TYPE SystemV lvls types)
                       -> TermBuilder (BinPorts types)
binGatePorts portOUT portInA portInB
  = do (MkDPair tyO pout) <- isPortWithDir portOUT OUT
       (MkDPair tyA pina) <- isPortWithDir portInA IN
       (MkDPair tyB pinb) <- isPortWithDir portInB IN
       case DataTypes.decEq tyO tyA of
         (Yes prfOA) =>
           case DataTypes.decEq tyA tyB of
             (Yes prfAB) => Right (mkBin pout pina pinb prfOA prfAB)

             (No msgWhyNot prfWhyNot) =>
               Left (TypeMismatch tyA tyB)
         (No msgWhyNot prfWhyNot) =>
           Left (TypeMismatch tyO tyA)

export
canCast : {lvls  : Universes}
       -> {types : Context lvls}
       -> (port  : Result TYPE SystemV lvls types)
       -> (toTy  : Result TYPE SystemV lvls types)
       -> (toDir : Direction)
                -> TermBuilder (Result TYPE SystemV lvls types)
canCast port toTy toDir with (view isPort port)
  canCast (Res u type term) toTy toDir | (HasView prf) with (type)
    canCast (Res (IDX TERM) type term) toTy toDir | (HasView Match) | (PortTy ty dir) with (view isData toTy)
      canCast (Res (IDX TERM) type termP) (Res u tyD termD) toDir | (HasView Match) | (PortTy tyF dirF) | (HasView prf) with (tyD)
        canCast (Res (IDX TERM) type termP) (Res (DATA TYPE) tyD termD) toDir | (HasView Match) | (PortTy tyF dirF) | (HasView Match) | toDataType with (validCast (PortTy tyF dirF) (PortTy toDataType toDir))
          canCast (Res (IDX TERM) type termP) (Res (DATA TYPE) tyD termD) toDir | (HasView Match) | (PortTy tyF dirF) | (HasView Match) | toDataType | (Yes prfWhy)
            = Right (Res _ _ (Cast termP prfWhy))
          canCast (Res (IDX TERM) type termP) (Res (DATA TYPE) tyD termD) toDir | (HasView Match) | (PortTy tyF dirF) | (HasView Match) | toDataType | (No msgWhyNot prfWhyNot)
            = Left (InvalidCast msgWhyNot (PortTy tyF dirF) (PortTy toDataType toDir))
        canCast (Res (IDX TERM) type termP) (Res u tyD termD) toDir | (HasView Match) | (PortTy tyF dirF) | (HasView Fail) | toDataType
          = Left (WrongType (NotADataType InCast) toDataType)

    canCast (Res u type term) toTy toDir | (HasView Fail) | type'
      = Left (WrongType NotAPort type')

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
connectPorts a b with (view isPort a)
  connectPorts (Res u typeA termA) b | (HasView prf) with (typeA)
    connectPorts (Res (IDX TERM) typeA termA) b | (HasView Match) | (PortTy tyA dirA) with (view isPort b)
      connectPorts (Res (IDX TERM) typeA termA) (Res u typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView prf) with (typeB)
        connectPorts (Res (IDX TERM) typeA termA) (Res (IDX TERM) typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Match) | (PortTy tyB dirB) with (DataTypes.decEq tyA tyB)
          connectPorts (Res (IDX TERM) typeA termA) (Res (IDX TERM) typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Match) | (PortTy tyB dirB) | (Yes prfWhy) with (prfWhy)
            connectPorts (Res (IDX TERM) typeA termA) (Res (IDX TERM) typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Match) | (PortTy tyA dirB) | (Yes prfWhy) | (Same Refl Refl) with (validFlow dirA dirB)
              connectPorts (Res (IDX TERM) typeA termA) (Res (IDX TERM) typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Match) | (PortTy tyA dirB) | (Yes prfWhy) | (Same Refl Refl) | (Yes prfFlow) = Right (CP termA termB prfFlow)
              connectPorts (Res (IDX TERM) typeA termA) (Res (IDX TERM) typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Match) | (PortTy tyA dirB) | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
                = Left (InvalidFlow msgWhyNot)
          connectPorts (Res (IDX TERM) typeA termA) (Res (IDX TERM) typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Match) | (PortTy tyB dirB) | (No msgWhyNot prfWhyNot)
            = Left (TypeMismatch tyA tyB)

        connectPorts (Res (IDX TERM) typeA termA) (Res u typeB termB) | (HasView Match) | (PortTy tyA dirA) | (HasView Fail) | typeB'
          = Left (WrongType (NotAPort) typeB')
    connectPorts (Res u typeA termA) b | (HasView Fail) | typeA'
      = Left (WrongType (NotAPort) typeA')

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
application fun arg with (view isFunc fun)
  application (Res u type term) arg | (HasView prf) with (type)
    application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a b) with (isTerm arg)
      application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a b) | (Left err)
        = Left err
      application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a b) | (Right (T a' x)) with (Equality.decEq a a')
        application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a b) | (Right (T a' x)) | (Yes prfWhy) with (prfWhy)
          application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a b) | (Right (T a' x)) | (Yes prfWhy) | (Same prfIdx prfVal) with (prfVal)
            application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a' b) | (Right (T a' x)) | (Yes prfWhy) | (Same Refl Refl) | Refl
              = Right (APP term x)
        application (Res (IDX TERM) type term) arg | (HasView Match) | (FuncTy a b) | (Right (T a' x)) | (No msgWhyNot prfWhyNot)
          = Left (TypeMismatch a a')
    application (Res (IDX _) type term) arg | (HasView WrongTm) | ty'
      = Left (WrongType NotAFunc ty')
    application (Res u type term) arg | (HasView NotATerm) | ty'
      = Left (WrongType NotAFunc ty')


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
annotation type with (isType type)
  annotation type | (Left err)
    = Left err
  annotation type | (Right (TT ty termTy)) with (synthesis ty)
    annotation type | (Right (TT ty termTy)) | (Yes (MkDPair argty (Synth argty prfarg prfret chk)))
      = Right (ANN ty termTy argty chk)

    annotation type | (Right (TT ty termTy)) | (No msgWhyNot prfWhyNot)
      = Left (InvalidFuncSynth msgWhyNot ty)

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
body a type with (isTermTerm type)
  body a type | (Left err)
    = Left err
  body a type | (Right (TTerm ty term)) with (Function.validTerm (IDX TERM) (FuncTy a ty))
    body a type | (Right (TTerm ty term)) | (Yes prfWhy)
      = Right (B term prfWhy)
    body a type | (Right (TTerm ty term)) | (No msgWhyNot prfWhyNot)
      = Left (InvalidFunc msgWhyNot a ty)




-- [ EOF ]
