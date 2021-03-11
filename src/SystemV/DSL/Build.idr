module SystemV.DSL.Build

import        Decidable.Equality

import        Data.Vect
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Toolkit.Data.Location
import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem

import        SystemV.Types
import        SystemV.Terms

import        SystemV.DSL.AST
import        SystemV.Utilities

%default total


public export
data Error = MkError
           | LeftSeqNotUnit
           | RightSeqNotValue
           | CannotBindNonIdx
           | NotAPort
           | NotADataType
           | InvalidPortCast
           | InvalidConnect
           | NotAChan
           | NotAFunc
           | NotAFuncParam
           | TypeMismatch
           | NotAType
           | NoHigherOrderStuff
           | ChansAreNotPorts
           | NotAValidCondTest
           | NotAName

export
Show Build.Error where
  show MkError            = "MkError"
  show LeftSeqNotUnit     = "LeftSeqNotUnit"
  show RightSeqNotValue   = "RightSeqNotValue"
  show CannotBindNonIdx   = "CannotBindNonIdx"
  show NotAPort           = "NotAPort"
  show NotADataType       = "NotADataType"
  show InvalidPortCast    = "InvalidPortCast"
  show InvalidConnect     = "InvalidConnect"
  show NotAChan           = "NotAChan"
  show NotAFunc           = "NotAFunc"
  show NotAFuncParam      = "NotAFuncParam"
  show TypeMismatch       = "TypeMismatch"
  show NotAType           = "NotAType"
  show NoHigherOrderStuff = "NoHigherOrderStuff"
  show ChansAreNotPorts   = "ChansAreNotPorts"
  show NotAValidCondTest  = "NotAValidCondTest"
  show NotAName           = "NotAName"

public export
Build : Type -> Type
Build = Either Build.Error

data Name : (u : Universe) -> Type where
  MkName : (s : Maybe String) -> (lvl : Universe) -> Name lvl

data HasName : (s : String) -> (lvl : Universe) -> (thing : Name lvl) -> Type where
  YesHasName : (s === x) -> HasName s lvl (MkName (Just x) lvl)

noname : HasName s lvl (MkName Nothing lvl) -> Void
noname (YesHasName _) impossible

wrongName : (contra : s === x -> Void)
         -> (prf    : HasName s lvl (MkName (Just x) lvl))
                   -> Void
wrongName contra (YesHasName Refl) = contra Refl

hasName : (s : String) -> (lvl : Universe) -> (thing : Name lvl) -> Dec (HasName s lvl thing)
hasName s lvl (MkName Nothing lvl) = No noname
hasName s lvl (MkName (Just x) lvl) with (decEq s x)
  hasName s lvl (MkName (Just x) lvl) | (Yes prf) = Yes (YesHasName prf)
  hasName s lvl (MkName (Just x) lvl) | (No contra) = No (wrongName contra)

Names : Universes -> Type
Names = DList Universe Name

data BuildCtxt : (lvls : Universes)
              -> (ctxt : Context lvls)
                      -> Type
  where
    Ctxt : (lvls : Universes)
        -> (names : Names lvls)
        -> (ctxt : Context lvls)
                -> BuildCtxt lvls ctxt

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


data ValidFuncParam : (level : Universe)
                   -> (type  : Meta level) -> Type where
  IsPort  : ValidFuncParam (IDX TYPE) (PortTy x dir)
  IsParam : ValidFuncParam (IDX TYPE) ParamTy
  IsUnit  : ValidFuncParam (IDX TYPE) UnitTy


isDataType : ValidFuncParam (DATA TYPE) type -> Void
isDataType IsPort impossible
isDataType IsParam impossible
isDataType IsUnit impossible

isDataValue : ValidFuncParam (DATA VALUE) type -> Void
isDataValue IsPort impossible
isDataValue IsParam impossible
isDataValue IsUnit impossible

isIdxValue : ValidFuncParam (IDX VALUE) type -> Void
isIdxValue IsPort impossible
isIdxValue IsParam impossible
isIdxValue IsUnit impossible

isModule  : ValidFuncParam (IDX TYPE) ModuleTyDesc -> Void
isModule IsPort impossible
isModule IsParam impossible
isModule IsUnit impossible

isFunc  : ValidFuncParam (IDX TYPE) (FuncTy x y) -> Void
isFunc IsPort impossible
isFunc IsParam impossible
isFunc IsUnit impossible

isChan  : ValidFuncParam (IDX TYPE) (ChanTy t) -> Void
isChan IsPort impossible
isChan IsParam impossible
isChan IsUnit impossible

validFuncParam : (level : Universe)
              -> (type  : Meta level)
              -> Dec (ValidFuncParam level type)
validFuncParam (IDX TYPE) (FuncTy x y) = No isFunc
validFuncParam (IDX TYPE) ModuleTyDesc = No isModule
validFuncParam (IDX TYPE) (ChanTy type) = No isChan
validFuncParam (IDX TYPE) (PortTy type dir) = Yes IsPort
validFuncParam (IDX TYPE) ParamTy = Yes IsParam
validFuncParam (IDX TYPE) UnitTy = Yes IsUnit

validFuncParam (IDX VALUE) type = No isIdxValue
validFuncParam (DATA VALUE) type = No isDataValue
validFuncParam (DATA TYPE) type = No isDataType

data ValidFuncParamValue : (level : Universe)
                        -> (type  : Meta level)
                        -> (value : Meta (IDX VALUE))
                                 -> Type where
   VFPV : ValidFuncParam (IDX TYPE) type -> (value : Meta (IDX VALUE)) -> ValidFuncParamValue (IDX TYPE) type value

isNotValidFPV : (contra : ValidFuncParam level type -> Void)
             -> (prf    : (value ** ValidFuncParamValue level type value))
                       -> Void
isNotValidFPV contra (MkDPair fst (VFPV x fst)) = contra x

validFuncParamValue : (level : Universe)
                   -> (type  : Meta level)
                            -> Dec (value ** ValidFuncParamValue level type value)
validFuncParamValue level type with (validFuncParam level type)
  validFuncParamValue (IDX TYPE) (PortTy x dir) | (Yes IsPort)
    = Yes (_ ** VFPV IsPort (PortVal x dir))
  validFuncParamValue (IDX TYPE) ParamTy | (Yes IsParam)
    = Yes (_ ** VFPV IsParam ParamVal)
  validFuncParamValue (IDX TYPE) UnitTy | (Yes IsUnit)
    = Yes (_ ** VFPV IsUnit UnitVal)
  validFuncParamValue level type | (No contra)
    = No (isNotValidFPV contra)

data ValidFuncTy : (level : Universe)
                -> (type  : Meta level)
                         -> Type
  where
    IsValid  : ValidFuncParamValue (IDX TYPE) type value
            -> TyCheck type value
            -> ValidFuncTy (IDX TYPE) type
    IsValidNot : ValidFuncTy (IDX TYPE) rest
    IsNotAType : ValidFuncTy level type

isFuncTy : (level : Universe) -> (type : Meta level) -> ValidFuncTy level type
isFuncTy (IDX TYPE) type with (validFuncParamValue (IDX TYPE) type)
  isFuncTy (IDX TYPE) type | (Yes (value ** VFPV x value)) with (typeCheck type value)
    isFuncTy (IDX TYPE) type | (Yes (value ** VFPV x value)) | (Yes prfWhy) = IsValid (VFPV x value) prfWhy

    isFuncTy (IDX TYPE) type | (Yes (value ** VFPV x value)) | (No msgWhyNot prfWhyNot) = IsValidNot -- really an internal error
  isFuncTy (IDX TYPE) type | (No contra) = IsValidNot
isFuncTy _ _ = IsNotAType


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


isName : (name  : String)
       -> (names : Names lvls)
       -> Dec (level ** Elem Universe Name (MkName (Just name) level) names)
isName name [] = No listEmpty
isName name ((MkName Nothing x) :: rest) with (isName name rest)
  isName name ((MkName Nothing x) :: rest) | (Yes (MkDPair fst snd)) = Yes (MkDPair fst (T snd))
  isName name ((MkName Nothing x) :: rest) | (No contra) = No (Build.notInLater contra)
isName name ((MkName (Just y) x) :: rest) with (hasName name x (MkName (Just y) x))
  isName y ((MkName (Just y) x) :: rest) | (Yes (YesHasName Refl)) = Yes (MkDPair x (H (Same Refl Refl)))
  isName name ((MkName (Just y) x) :: rest) | (No contra) with (isName name rest)
    isName name ((MkName (Just y) x) :: rest) | (No contra) | (Yes (MkDPair fst snd)) = Yes (MkDPair fst (T snd))
    isName name ((MkName (Just y) x) :: rest) | (No contra) | (No f) = No (nameNotInRest contra f)

buildProof : {names : Names lvls}
          -> (prf   : Elem Universe Name (MkName (Just name) level) names)
          -> (ctxt  : Context lvls)
          -> (type : Meta level ** Elem Universe Meta type ctxt)
buildProof (H (Same Refl prfVal)) (elem :: rest) = MkDPair elem (H (Same Refl Refl))
buildProof (T later) (elem :: rest) with (buildProof later rest)
  buildProof (T later) (elem :: rest) | (MkDPair fst snd) = MkDPair fst (T snd)


build : (env : BuildCtxt lvls ctxt)
     -> (ast : AST)
            -> Build (BuildRes lvls ctxt)
build env ast with (env)
  build env ast | (Ctxt lvls names ctxt) with (ast)
    build env ast | (Ctxt lvls names ctxt) | (Ref fc name) with (isName name names)
      build env ast | (Ctxt lvls names ctxt) | (Ref fc name) | (Yes (MkDPair fst snd)) with (buildProof snd ctxt)
        build env ast | (Ctxt lvls names ctxt) | (Ref fc name) | (Yes (MkDPair fst snd)) | (MkDPair x y)
          = pure (Res _ _ (Var y))
      build env ast | (Ctxt lvls names ctxt) | (Ref fc name) | (No contra)
        = Left NotAName

    build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) with (build (Ctxt lvls names ctxt) type)
      build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res u meta term)) with (isFuncTy u meta)
        build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res (IDX TYPE) meta term)) | (IsValid (VFPV x value) y) with (build (Ctxt (IDX VALUE :: lvls) (MkName (Just name) (IDX VALUE) :: names) (value::ctxt)) body)
          build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res (IDX TYPE) meta term)) | (IsValid (VFPV x value) y) | (Left err)
             = Left err
          build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res (IDX TYPE) meta term)) | (IsValid (VFPV x value) y) | (Right (Res (IDX VALUE) bodyType bodyTerm))
            = pure (Res _ _ (Func term bodyTerm y))
          build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res (IDX TYPE) meta term)) | (IsValid (VFPV x value) y) | (Right (Res _ _ _))
            = Left MkError
        build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res (IDX TYPE) meta term)) | IsValidNot
          = Left NoHigherOrderStuff
        build env ast | (Ctxt lvls names ctxt) | (Func fc name type body) | (Right (Res u meta term)) | IsNotAType
          = Left NotAType

    build env ast | (Ctxt lvls names ctxt) | (App func param) with (build (Ctxt lvls names ctxt) func)
      build env ast | (Ctxt lvls names ctxt) | (App func param) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) with (build (Ctxt lvls names ctxt) param)
        build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) | (Right (Res (IDX VALUE) typeParam term)) with (decEqTypeValues paramTy typeParam)
          build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) | (Right (Res (IDX VALUE) typeParam term)) | (Yes prfWhy) with (prfWhy)
            build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) | (Right (Res (IDX VALUE) paramTy term)) | (Yes prfWhy) | (Same Refl Refl)
              = pure (Res _ _ (App funcTerm term))
          build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) | (Right (Res (IDX VALUE) typeParam term)) | (No msgWhyNot prfWhyNot)
            = Left TypeMismatch
        build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res (IDX VALUE) (FuncTy paramTy bodyTy) funcTerm)) | (Right (Res _ _ _))
          = Left NotAFuncParam
      build env ast | (Ctxt lvls names ctxt) | (App func param) | (Right (Res _ _ _))
        = Left NotAFunc

    build env ast | (Ctxt lvls names ctxt) | (TyLogic fc)
      = pure (Res _ _ TyLogic)

    build env ast | (Ctxt lvls names ctxt) | (TyVect fc s type) with (build (Ctxt lvls names ctxt) type)
      build env ast | (Ctxt lvls names ctxt) | (TyVect fc s type) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (TyVect fc s type) | (Right (Res (DATA TYPE) typeData termData))
        = pure (Res _ _ (TyVect s termData))
      build env ast | (Ctxt lvls names ctxt) | (TyVect fc s type) | (Right (Res _ _ _))
        = Left NotADataType


    build env ast | (Ctxt lvls names ctxt) | (TypeDef fc name type body) with (build (Ctxt lvls names ctxt) type)
      build env ast | (Ctxt lvls names ctxt) | (TypeDef fc name type body) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (TypeDef fc name type body) | (Right (Res (DATA TYPE) typeData termData)) with (build (Ctxt (DATA TYPE::lvls) (MkName (Just name) (DATA TYPE) :: names) (TypeDefTy typeData :: ctxt)) body)
        build env ast | (Ctxt lvls names ctxt) | (TypeDef fc name type body) | (Right (Res (DATA TYPE) typeData termData)) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (TypeDef fc name type body) | (Right (Res (DATA TYPE) typeData termData)) | (Right (Res u x body'))
          = pure (Res _ _ (TypeDef (TypeDefType termData) body'))
      build env ast | (Ctxt lvls names ctxt) | (TypeDef fc name type body) | (Right (Res _ _ _))
        = Left NotADataType

    build env ast | (Ctxt lvls names ctxt) | (TyPort fc type dir) with (build (Ctxt lvls names ctxt) type)
      build env ast | (Ctxt lvls names ctxt) | (TyPort fc type dir) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (TyPort fc type dir) | (Right (Res (DATA TYPE) x term))
        = pure (Res _ _ (TyPort term dir))
      build env ast | (Ctxt lvls names ctxt) | (TyPort fc type dir) | (Right (Res _ _ _))
        = Left NotADataType

    build env ast | (Ctxt lvls names ctxt) | (MkChan fc type) with (build (Ctxt lvls names ctxt) type)
      build env ast | (Ctxt lvls names ctxt) | (MkChan fc type) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (MkChan fc type) | (Right (Res (DATA TYPE) x term))
        = pure (Res _ _ (MkChan term))
      build env ast | (Ctxt lvls names ctxt) | (MkChan fc type) | (Right (Res _ _ _))
        = Left NotADataType

    build env ast | (Ctxt lvls names ctxt) | (WriteTo fc chan) with (build (Ctxt lvls names ctxt) chan)
      build env ast | (Ctxt lvls names ctxt) | (WriteTo fc chan) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (WriteTo fc chan) | (Right (Res (IDX VALUE) (ChanVal type) term))
        = pure (Res _ _ (WriteTo term))
      build env ast | (Ctxt lvls names ctxt) | (WriteTo fc chan) | (Right (Res _ _ _))
        = Left NotAChan

    build env ast | (Ctxt lvls names ctxt) | (ReadFrom fc chan) with (build (Ctxt lvls names ctxt) chan)
      build env ast | (Ctxt lvls names ctxt) | (ReadFrom fc chan) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (ReadFrom fc chan) | (Right (Res (IDX VALUE) (ChanVal type) term))
        = pure (Res _ _ (ReadFrom term))
      build env ast | (Ctxt lvls names ctxt) | (ReadFrom fc chan) | (Right (Res _ _ _))
        = Left NotAChan

    build env ast | (Ctxt lvls names ctxt) | (Drive fc chan) with (build (Ctxt lvls names ctxt) chan)
      build env ast | (Ctxt lvls names ctxt) | (Drive fc chan) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Drive fc chan) | (Right (Res (IDX VALUE) (ChanVal type) term))
        = pure (Res _ _ (Drive term))
      build env ast | (Ctxt lvls names ctxt) | (Drive fc chan) | (Right (Res _ _ _))
        = Left NotAChan

    build env ast | (Ctxt lvls names ctxt) | (Catch fc chan) with (build (Ctxt lvls names ctxt) chan)
      build env ast | (Ctxt lvls names ctxt) | (Catch fc chan) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Catch fc chan) | (Right (Res (IDX VALUE) (ChanVal type) term))
        = pure (Res _ _ (Catch term))
      build env ast | (Ctxt lvls names ctxt) | (Catch fc chan) | (Right (Res _ _ _))
        = Left NotAChan


    build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) with (build (Ctxt lvls names ctxt) test)
      build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Left err)
        = Left err

      build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) with (build (Ctxt lvls names ctxt) true)
        build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) | (Right (Res (IDX VALUE) UnitVal x)) with (build (Ctxt lvls names ctxt) false)
          build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) | (Right (Res (IDX VALUE) UnitVal x)) | (Left err)
            = Left err
          build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) | (Right (Res (IDX VALUE) UnitVal x)) | (Right (Res (IDX VALUE) UnitVal y))
            = pure (Res _ _ (IfThenElseC term x y))
          build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) | (Right (Res (IDX VALUE) UnitVal x)) | (Right (Res _ _ _))
            = Left TypeMismatch
        build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (DATA VALUE) BoolTy term)) | (Right (Res _ _ _))
          = Left TypeMismatch

      build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) with (build (Ctxt lvls names ctxt) true)
        build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) | (Right (Res (IDX VALUE) UnitVal y)) with (build (Ctxt lvls names ctxt) false)
          build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) | (Right (Res (IDX VALUE) UnitVal y)) | (Left err)
            = Left err
          build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) | (Right (Res (IDX VALUE) UnitVal y)) | (Right (Res (IDX VALUE) UnitVal z))
            = pure (Res _ _ (IfThenElseR term y z))
          build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) | (Right (Res (IDX VALUE) UnitVal y)) | (Right (Res _ _ _))
            = Left TypeMismatch
        build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res (IDX VALUE) (PortVal type IN) term)) | (Right (Res _ _ _))
          = Left TypeMismatch
      build env ast | (Ctxt lvls names ctxt) | (IfThenElse fc test true false) | (Right (Res _ _ _))
        = Left NotAValidCondTest


    build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) with (build (Ctxt lvls names ctxt) portL)
      build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) with (build (Ctxt lvls names ctxt) portR)
        build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res (IDX VALUE) (PortVal typeB dirR) portRTerm)) with (decEqTypesDataTypes typeA typeB)
          build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res (IDX VALUE) (PortVal typeB dirR) portRTerm)) | (Yes prfWhy) with (prfWhy)
            build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res (IDX VALUE) (PortVal typeA dirR) portRTerm)) | (Yes prfWhy) | (Same Refl Refl) with (validFlow dirL dirR)
              build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res (IDX VALUE) (PortVal typeA dirR) portRTerm)) | (Yes prfWhy) | (Same Refl Refl) | (Yes prfValidFlow)
                = pure (Res _ _ (Connect portLTerm portRTerm prfValidFlow))
              build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res (IDX VALUE) (PortVal typeA dirR) portRTerm)) | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
                = Left InvalidConnect
          build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res (IDX VALUE) (PortVal typeB dirR) portRTerm)) | (No msgWhyNot prfWhyNot)
            = Left InvalidConnect
        build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res (IDX VALUE) (PortVal typeA dirL) portLTerm)) | (Right (Res _ _ _))
          = Left NotAPort
      build env ast | (Ctxt lvls names ctxt) | (Connect fc portL portR) | (Right (Res _ _ _))
        = Left NotAPort


    build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) with (build (Ctxt lvls names ctxt) port)
      build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res (IDX VALUE) (PortVal dtype fromDir) term)) with (build  (Ctxt lvls names ctxt) type)
        build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res (IDX VALUE) (PortVal dtype fromDir) term)) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res (IDX VALUE) (PortVal dtype fromDir) term)) | (Right (Res (IDX TYPE) (PortTy dTypeTo toDir) type')) with (validCast (PortVal dtype fromDir) (PortVal dTypeTo toDir))
          build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res (IDX VALUE) (PortVal dtype fromDir) term)) | (Right (Res (IDX TYPE) (PortTy dTypeTo toDir) type')) | (Yes prfWhy)
            = pure (Res _ _ (Cast term prfWhy))
          build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res (IDX VALUE) (PortVal dtype fromDir) term)) | (Right (Res (IDX TYPE) (PortTy dTypeTo toDir) type')) | (No msgWhyNot prfWhyNot)
            = Left InvalidPortCast
        build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res (IDX VALUE) (PortVal dtype fromDir) term)) | (Right (Res _ _ _))
          = Left NotAPort
      build env ast | (Ctxt lvls names ctxt) | (Cast fc port type dir) | (Right (Res _ _ _))
        = Left NotAPort


    build env ast | (Ctxt lvls names ctxt) | TyParam
      = pure (Res _ _ TyParam)
    build env ast | (Ctxt lvls names ctxt) | (MkParam fc val)
      = pure (Res _ _ (MkParam val))

    build env ast | (Ctxt lvls names ctxt) | (ParamOpBool fc op left right)
      = do (Res (IDX VALUE) ParamVal l) <- build (Ctxt lvls names ctxt) left
              | _ => Left MkError

           (Res (IDX VALUE) ParamVal r) <- build (Ctxt lvls names ctxt) right
              | _ => Left MkError

           pure (Res _ _ (ParamOpBool op l r))

    build env ast | (Ctxt lvls names ctxt) | (ParamOpNot fc op)
      = do (Res (DATA VALUE) BoolTy t) <- build (Ctxt lvls names ctxt) op
              | _ => Left MkError
           pure (Res _ _ (ParamOpNot t))

    build env ast | (Ctxt lvls names ctxt) | (ParamOpArith fc op left right)
      = do (Res (IDX VALUE) ParamVal l) <- build (Ctxt lvls names ctxt) left
              | _ => Left MkError
           (Res (IDX VALUE) ParamVal r) <- build (Ctxt lvls names ctxt) right
              | _ => Left MkError
           pure (Res _ _ (ParamOpArith op l r))


    build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) with (build (Ctxt lvls names ctxt) value)
      build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) | (Right (Res (IDX VALUE) type value')) with (build (Ctxt (IDX VALUE::lvls) (MkName (Just name) (IDX VALUE)::names) (type::ctxt)) body)
        build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) | (Right (Res (IDX VALUE) type value')) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) | (Right (Res (IDX VALUE) type value')) | (Right (Res (IDX VALUE) typeB body'))
          = pure (Res _ _ (Let value' body'))
        build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) | (Right (Res (IDX VALUE) type value')) | (Right (Res _ _ _))
          = Left MkError
      build env ast | (Ctxt lvls names ctxt) | (Let fc name value body) | (Right (Res _ type value'))
        = Left CannotBindNonIdx

    build env ast | (Ctxt lvls names ctxt) | (Seq x y) with (build (Ctxt lvls names ctxt) x)
      build env ast | (Ctxt lvls names ctxt) | (Seq x y) | (Left err)
        = Left err
      build env ast | (Ctxt lvls names ctxt) | (Seq x y) | (Right (Res (IDX VALUE) UnitVal x')) with (build (Ctxt (IDX VALUE :: lvls) (MkName Nothing (IDX VALUE) :: names) (UnitVal :: ctxt)) y)
        build env ast | (Ctxt lvls names ctxt) | (Seq x y) | (Right (Res (IDX VALUE) UnitVal x')) | (Left err)
          = Left err
        build env ast | (Ctxt lvls names ctxt) | (Seq x y) | (Right (Res (IDX VALUE) UnitVal x')) | (Right (Res (IDX VALUE) ty y'))
          = pure (Res _ _ (seq x' y'))
        build env ast | (Ctxt lvls names ctxt) | (Seq x y) | (Right (Res (IDX VALUE) UnitVal x')) | (Right (Res _ _ _))
          = Left RightSeqNotValue
      build env ast | (Ctxt lvls names ctxt) | (Seq x y) | (Right (Res u _ x'))
        = Left LeftSeqNotUnit

    build env ast | (Ctxt lvls names ctxt) | EndModule
      = pure (Res _ _ EndModule)
    build env ast | (Ctxt lvls names ctxt) | UnitVal
      = pure (Res _ _ MkUnit)
    build env ast | (Ctxt lvls names ctxt) | TyUnit
      = pure (Res _ _ TyUnit)

export
metaTypeCheck : (ast : AST)
                   -> Build (BuildRes Nil Nil)
metaTypeCheck ast with (build (Ctxt Nil Nil Nil) ast)
  metaTypeCheck ast | (Left x) = Left x
  metaTypeCheck ast | (Right (Res u type term)) = Right (Res u type term)

-- --------------------------------------------------------------------- [ EOF ]
