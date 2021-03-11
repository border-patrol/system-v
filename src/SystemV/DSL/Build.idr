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
import        SystemV.DSL.Build.Context
import        SystemV.DSL.Build.Helpers
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

build : (env : BuildCtxt lvls ctxt)
     -> (ast : AST)
            -> Build (BuildRes lvls ctxt)
build env ast with (env)
  build env ast | (Ctxt lvls names ctxt) with (ast)
    build env ast | (Ctxt lvls names ctxt) | (Ref fc name) with (isName name names)
      build env ast | (Ctxt lvls names ctxt) | (Ref fc name) | (Yes (MkDPair fst snd)) with (buildVar snd ctxt)
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
