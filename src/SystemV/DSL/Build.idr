module SystemV.DSL.Build

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

import        SystemV.Utilities

import        SystemV.Types
import        SystemV.Terms

import        SystemV.DSL.AST
import        SystemV.DSL.Build.Context
import        SystemV.DSL.Build.Result
import        SystemV.DSL.Build.Helpers
import public SystemV.DSL.Build.Error

%default total


public export
TermBuilder : Type -> Type
TermBuilder = Either Build.Error

termBuilder : (ctxt : Context lvls types)
           -> (ast  : AST)
                   -> TermBuilder (Result lvls types)
-- ## Types

-- ### Unit
termBuilder (Ctxt lvls names types) TyUnit
  = pure (Res _ _ TyUnit)

-- ### Logic
termBuilder (Ctxt lvls names types) (TyLogic fc)
  = pure (Res _ _ TyLogic)

-- ### Vectors
termBuilder ctxt (TyVect fc size type) with (isWhole size)

-- Right size
  termBuilder ctxt (TyVect fc (S n) type) | (Yes YesIsWhole) with (termBuilder ctxt type)
    termBuilder ctxt (TyVect fc (S n) type) | (Yes YesIsWhole) | (Left err)
      = Left (Err fc err)

    termBuilder ctxt (TyVect fc (S n) type) | (Yes YesIsWhole) | (Right (Res (DATA TYPE) x term))
      = pure (Res _ _ (TyVect (W (S n) ItIsSucc) term))

    termBuilder ctxt (TyVect fc (S n) type) | (Yes YesIsWhole) | (Right (Res u ty _))
      = Left (Err fc (WrongType (NotADataType InVector) ty))

-- Has Size Zero
  termBuilder ctxt (TyVect fc size type) | (No contra)
    = Left (Err fc VectorSizeZero)

-- ### Type-Definitions
termBuilder ctxt (TypeDef fc name type body) with (termBuilder ctxt type)
  termBuilder ctxt (TypeDef fc name type body) | (Left err)
    = Left (Err fc err)

  termBuilder (Ctxt lvls names types) (TypeDef fc name type body) | (Right (Res (DATA TYPE) typeT termT)) with (termBuilder (Ctxt (DATA TYPE::lvls) (MkName (Just name) (DATA TYPE) :: names) (TypeDefTy typeT :: types)) body)
    termBuilder (Ctxt lvls names types) (TypeDef fc name type body) | (Right (Res (DATA TYPE) typeT termT)) | (Left err)
      = Left (Err fc err)

    termBuilder (Ctxt lvls names types) (TypeDef fc name type body) | (Right (Res (DATA TYPE) typeT termT)) | (Right (Res u typeB termB))
      = pure (Res _ _ (Let (TyTypeDef termT) termB))

  termBuilder ctxt (TypeDef fc name type body) | (Right (Res u ty _))
    = Left (Err fc (WrongType (NotADataType InTypeDef) ty))

-- ### Ports
termBuilder ctxt (TyPort fc type dir) with (termBuilder ctxt type)
  termBuilder ctxt (TyPort fc type dir) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (TyPort fc type dir) | (Right (Res (DATA TYPE) typeT term))
    = pure (Res _ _ (TyPort term dir))

  termBuilder ctxt (TyPort fc type dir) | (Right (Res u typeT _))
    = Left (Err fc (WrongType (NotADataType InPort) typeT))

-- ## STLC

-- ### References
termBuilder (Ctxt lvls names types) (Ref fc name) with (isName name names)
  termBuilder (Ctxt lvls names types) (Ref fc name) | (Yes (MkDPair level idx_name)) with (mkVar idx_name types)
    termBuilder (Ctxt lvls names types) (Ref fc name) | (Yes (MkDPair level idx_name)) | (MkDPair type idx)
      = pure (Res _ _ (Var idx))
  termBuilder (Ctxt lvls names types) (Ref fc name) | (No contra)
    = Left (Err fc (NotAName name))

-- ### Functions
termBuilder ctxt (Func fc name type body) with (termBuilder ctxt type)
  termBuilder ctxt (Func fc name type body) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) with (synthesis typeTy)
    termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (Yes (MkDPair argTy (Synth argTy prfArg prfRet prfCheck))) with (termBuilder (Ctxt (IDX TERM :: lvls) (MkName (Just name) (IDX TERM) :: names) (argTy :: types)) body)
      termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (Yes (MkDPair argTy (Synth argTy prfArg prfRet prfCheck))) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (Yes (MkDPair argTy (Synth argTy prfArg prfRet prfCheck))) | (Right (Res (IDX TERM) bodyTy termBody)) with (Function.validTerm (IDX TERM) (FuncTy argTy bodyTy))
        termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (Yes (MkDPair argTy (Synth argTy prfArg prfRet prfCheck))) | (Right (Res (IDX TERM) bodyTy termBody)) | (Yes prfValid)
          = pure (Res _ _ (Func termType termBody prfCheck prfValid))
        termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (Yes (MkDPair argTy (Synth argTy prfArg prfRet prfCheck))) | (Right (Res (IDX TERM) bodyTy termBody)) | (No msgWhyNot prfWhyNot)
          = Left (Err fc (InvalidFunc msgWhyNot argTy bodyTy))

      termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (Yes (MkDPair argTy (Synth argTy prfArg prfRet prfCheck))) | (Right (Res u bodyTy termBody))
        = Left (Err fc (WrongType NotATerm bodyTy))


    termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right (Res (IDX TYPE) typeTy termType)) | (No msgWhyNot prfWhyNot)
      = Left (Err fc (InvalidFuncSynth msgWhyNot typeTy)) -- Internal Error...

  termBuilder ctxt (Func fc name type body) | (Right (Res levelTy typeTy _))
    = Left (Err fc (WrongType NotAType typeTy))

-- ### Application
termBuilder ctxt (App func param) with (termBuilder ctxt func)
  termBuilder ctxt (App func param) | (Left err)
    = Left err
  termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) with (termBuilder ctxt param)
    termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) | (Left err)
      = Left err
    termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) | (Right (Res (IDX TERM) paramTy termVal)) with (TypeTerms.decEq argTy paramTy)
      termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) | (Right (Res (IDX TERM) paramTy termVal)) | (Yes prfWhy) with (prfWhy) -- Why Idris, Why!
        termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) | (Right (Res (IDX TERM) argTy termVal)) | (Yes prfWhy) | (Same Refl Refl)
          = pure (Res _ _ (App funcTerm termVal))
      termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) | (Right (Res (IDX TERM) paramTy termVal)) | (No msgWhyNot prfWhyNot)
        = Left (TypeMismatch argTy paramTy)
    termBuilder ctxt (App func param) | (Right (Res (IDX TERM) (FuncTy argTy retTy) funcTerm)) | (Right (Res u type _))
      = Left (WrongType NotATerm type)
  termBuilder ctxt (App func param) | (Right (Res u type _))
    = Left (WrongType NotAFunc type)

-- ## Modules \& Units

termBuilder (Ctxt lvls names types) EndModule
  = pure (Res _ _ EndModule)

termBuilder (Ctxt lvls names types) UnitVal
  = pure (Res _ _ MkUnit)

-- ## Channels

-- ### Creation

termBuilder ctxt (MkChan fc type) with (termBuilder ctxt type)
  termBuilder ctxt (MkChan fc type) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (MkChan fc type) | (Right (Res (DATA TYPE) typeT term))
    = pure (Res _ _ (MkChan term))

  termBuilder ctxt (MkChan fc type) | (Right (Res u typeT _))
    = Left (Err fc (WrongType (NotADataType InChan) typeT))

-- ### Projection

-- #### Write To
termBuilder ctxt (WriteTo fc chan) with (termBuilder ctxt chan)
  termBuilder ctxt (WriteTo fc chan) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (WriteTo fc chan) | (Right (Res (IDX TERM) (ChanTy typeT) term))
    = pure (Res _ _ (WriteTo term))

  termBuilder ctxt (WriteTo fc chan) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAChannel typeT))

-- #### Read To
termBuilder ctxt (ReadFrom fc chan) with (termBuilder ctxt chan)
  termBuilder ctxt (ReadFrom fc chan) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (ReadFrom fc chan) | (Right (Res (IDX TERM) (ChanTy typeT) term))
    = pure (Res _ _ (ReadFrom term))

  termBuilder ctxt (ReadFrom fc chan) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAChannel typeT))

-- ### Driving

-- #### Drive

termBuilder ctxt (Drive fc port) with (termBuilder ctxt port)
  termBuilder ctxt (Drive fc port) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (Drive fc port) | (Right (Res (IDX TERM) (PortTy typeT OUT) term))
    = pure (Res _ _ (Drive term))

  termBuilder ctxt (Drive fc port) | (Right (Res (IDX TERM) (PortTy typeT dir) term))
    = Left (Err fc (TypeMismatch (PortTy typeT OUT) (PortTy typeT dir)))

  termBuilder ctxt (Drive fc port) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAPort typeT))

-- #### Catch
termBuilder ctxt (Catch fc port) with (termBuilder ctxt port)
  termBuilder ctxt (Catch fc port) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (Catch fc port) | (Right (Res (IDX TERM) (PortTy typeT IN) term))
    = pure (Res _ _ (Catch term))

  termBuilder ctxt (Catch fc port) | (Right (Res (IDX TERM) (PortTy typeT dir) term))
    = Left (Err fc (TypeMismatch (PortTy typeT IN) (PortTy typeT dir)))

  termBuilder ctxt (Catch fc port) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAPort typeT))

-- ## Operations on Ports

-- ### Casting
termBuilder ctxt (Cast fc port type dir) with (termBuilder ctxt port)
  termBuilder ctxt (Cast fc port type dir) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (Cast fc port type dir) | (Right (Res (IDX TERM) (PortTy typeD fromDir) fromTerm)) with (termBuilder ctxt type)
    termBuilder ctxt (Cast fc port type dir) | (Right (Res (IDX TERM) (PortTy typeD fromDir) fromTerm)) | (Left err)
      = Left (Err fc err)

    termBuilder ctxt (Cast fc port type dir) | (Right (Res (IDX TERM) (PortTy typeD fromDir) fromTerm)) | (Right (Res (IDX TERM) (PortTy typeTo toDir) toTerm)) with (validCast (PortTy typeD fromDir) (PortTy typeTo toDir))
      termBuilder ctxt (Cast fc port type dir) | (Right (Res (IDX TERM) (PortTy typeD fromDir) fromTerm)) | (Right (Res (IDX TERM) (PortTy typeTo toDir) toTerm)) | (Yes prfWhy)
        = pure (Res _ _ (Cast fromTerm prfWhy))
      termBuilder ctxt (Cast fc port type dir) | (Right (Res (IDX TERM) (PortTy typeD fromDir) fromTerm)) | (Right (Res (IDX TERM) (PortTy typeTo toDir) toTerm)) | (No msgWhyNot prfWhyNot)
        = Left (Err fc (InvalidCast msgWhyNot (PortTy typeD fromDir) (PortTy typeTo toDir)))

    termBuilder ctxt (Cast fc port type dir) | (Right (Res (IDX TERM) (PortTy typeD fromDir) fromTerm)) | (Right (Res u typeT _))
      = Left (Err fc (WrongType NotAPort typeT))

  termBuilder ctxt (Cast fc port type dir) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAPort typeT))

-- ### Slicing
termBuilder ctxt (Slice fc port s e) with (termBuilder ctxt port)
  termBuilder ctxt (Slice fc port s e) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Slice fc port s e) | (Right (Res (IDX TERM) (PortTy (VectorTyDesc size type) dir) term)) with (validBound s e size)
    termBuilder ctxt (Slice fc port s e) | (Right (Res (IDX TERM) (PortTy (VectorTyDesc size type) dir) term)) | (Yes prfWhy)
      = pure (Res _ _ (Slice term (MkNat s) (MkNat e) prfWhy))

    termBuilder ctxt (Slice fc port s e) | (Right (Res (IDX TERM) (PortTy (VectorTyDesc size type) dir) term)) | (No msgWhyNot prfWhyNot)
      = Left (Err fc (InvalidBound msgWhyNot))

  termBuilder ctxt (Slice fc port s e) | (Right (Res (IDX TERM) (PortTy type dir) term))
    = Left (Err fc (WrongType NotAVect (PortTy type dir)))

  termBuilder ctxt (Slice fc port s e) | (Right (Res u type _))
    = Left (Err fc (WrongType NotAPort type))

-- ### Conditionals

termBuilder ctxt (IfThenElse fc test true false) with (termBuilder ctxt test)
  termBuilder ctxt (IfThenElse fc test true false) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) with (termBuilder ctxt true)
    termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) | (Left err)
      = Left (Err fc err)


    termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) | (Right (Res (IDX TERM) UnitTy trueTerm)) with (termBuilder ctxt false)
      termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) | (Right (Res (IDX TERM) UnitTy trueTerm)) | (Left err)
        = Left (Err fc err)

      termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) | (Right (Res (IDX TERM) UnitTy trueTerm)) | (Right (Res (IDX TERM) UnitTy termFalse))
        = pure (Res _ _ (IfThenElseR term trueTerm termFalse))

      termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) | (Right (Res (IDX TERM) UnitTy trueTerm)) | (Right (Res u typeT _))
        = Left (Err fc (WrongType NotAUnit typeT))

    termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type IN) term)) | (Right (Res u typeT _))
      = Left (Err fc (WrongType NotAUnit typeT))

  termBuilder ctxt (IfThenElse fc test true false) | (Right (Res (IDX TERM) (PortTy type dir) term))
    = Left (Err fc (TypeMismatch (PortTy type IN) (PortTy type dir)))

  termBuilder ctxt (IfThenElse fc test true false) | (Right (Res u type term))
    = Left (Err fc (WrongType NotAPort type))

-- ### Connecting Ports
termBuilder ctxt (Connect fc portL portR) with (termBuilder ctxt portL)
  termBuilder ctxt (Connect fc portL portR) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) with (termBuilder ctxt portR)
    termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Left err)
      = Left (Err fc err)

    termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res (IDX TERM) (PortTy typeRight dirRight) right)) with (DataTypes.decEq typeLeft typeRight)
      termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res (IDX TERM) (PortTy typeRight dirRight) right)) | (Yes prfWhy) with (prfWhy) -- Why Idris, why!
        termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res (IDX TERM) (PortTy typeLeft dirRight) right)) | (Yes prfWhy) | (Same Refl Refl) with (validFlow dirLeft dirRight)
          termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res (IDX TERM) (PortTy typeLeft dirRight) right)) | (Yes prfWhy) | (Same Refl Refl) | (Yes x)
            = pure (Res _ _ (Connect left right x))

          termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res (IDX TERM) (PortTy typeLeft dirRight) right)) | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
            = Left (Err fc (InvalidFlow msgWhyNot))

      termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res (IDX TERM) (PortTy typeRight dirRight) right)) | (No msgWhyNot prfWhyNot)
        = Left (Err fc (TypeMismatch typeLeft typeRight))

    termBuilder ctxt (Connect fc portL portR) | (Right (Res (IDX TERM) (PortTy typeLeft dirLeft) left)) | (Right (Res u type term))
      = Left (Err fc (WrongType NotAPort type))

  termBuilder ctxt (Connect fc portL portR) | (Right (Res u type _))
    = Left (Err fc (WrongType NotAPort type))


-- ## Gates
termBuilder ctxt (NotGate fc portOut portIn) with (termBuilder ctxt portOut)
  termBuilder ctxt (NotGate fc portOut portIn) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) with (termBuilder ctxt portIn)
    termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Left err)
      = Left (Err fc err)

    termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Right (Res (IDX TERM) (PortTy typeIn IN) termIn)) with (DataTypes.decEq typeOut typeIn)
      termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Right (Res (IDX TERM) (PortTy typeIn IN) termIn)) | (Yes prfWhy) with (prfWhy)
        termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Right (Res (IDX TERM) (PortTy typeOut IN) termIn)) | (Yes prfWhy) | (Same Refl Refl)
          = Right (Res _ _ (Not termOut termIn))

      termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Right (Res (IDX TERM) (PortTy typeIn IN) termIn)) | (No msgWhyNot prfWhyNot)
        = Left (Err fc (TypeMismatch (typeOut) (typeIn)))

    termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Right (Res (IDX TERM) (PortTy typeIn dir) termIn))
      = Left (Err fc (TypeMismatch (PortTy typeIn OUT) (PortTy typeIn dir)))


    termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut OUT) termOut)) | (Right (Res u type _))
      = Left (Err fc (WrongType NotAPort type))

  termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res (IDX TERM) (PortTy typeOut dir) termOut))
    = Left (Err fc (TypeMismatch (PortTy typeOut OUT) (PortTy typeOut dir)))

  termBuilder ctxt (NotGate fc portOut portIn) | (Right (Res u type _))
    = Left (Err fc (WrongType NotAPort type))

termBuilder ctxt (Gate fc kind portOut portInA portInB) with (termBuilder ctxt portOut)
  termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) with (termBuilder ctxt portInA)
    termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Left err)
      = Left (Err fc err)

    termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) with (termBuilder ctxt portInB)
      termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Left err)
        = Left (Err fc err)
      termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB IN) termInB)) with (DataTypes.decEq typeO typeIA)
        termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB IN) termInB)) | (Yes prfWhy) with (prfWhy) -- Why Idris, Why!
          termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeIA OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB IN) termInB)) | (Yes prfWhy) | (Same Refl Refl) with (DataTypes.decEq typeIA typeIB)
            termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeIA OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB IN) termInB)) | (Yes prfWhy) | (Same Refl Refl) | (Yes prfWhyAB) with (prfWhyAB) -- Why Idris, Why!
              termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeIA OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInB)) | (Yes prfWhy) | (Same Refl Refl) | (Yes prfWhyAB) | (Same Refl Refl)
                = pure (Res _ _ (Gate kind termO termInA termInB))


            termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeIA OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB IN) termInB)) | (Yes prfWhy) | (Same Refl Refl) | (No msgWhyNot prfWhyNot)
              = Left (Err fc (TypeMismatch typeIA typeIB))

        termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB IN) termInB)) | (No msgWhyNot prfWhyNot)
          = Left (Err fc (TypeMismatch typeIA typeO))

      termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res (IDX TERM) (PortTy typeIB dir) termInB))
        = Left (Err fc (TypeMismatch (PortTy typeIB IN) (PortTy typeIB dir)))

      termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA IN) termInA)) | (Right (Res u type _))
        = Left (Err fc (WrongType NotAPort type))

    termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res (IDX TERM) (PortTy typeIA dir) term))
      = Left (Err fc (TypeMismatch (PortTy typeIA IN) (PortTy typeIA dir)))

    termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeO OUT) termO)) | (Right (Res u type _))
      = Left (Err fc (WrongType NotAPort type))

  termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res (IDX TERM) (PortTy typeOut dir) _))
    = Left (Err fc (TypeMismatch (PortTy typeOut OUT) (PortTy typeOut dir)))

  termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right (Res u type _))
    = Left (Err fc (WrongType NotAPort type))

--
termBuilder ctxt (Let fc name value body) with (termBuilder ctxt value)
  termBuilder ctxt (Let fc name value body) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Let fc name value body) | (Right (Res u typeV termV)) with (termBuilder (Ctxt (u::lvls) ((MkName (Just name) u)::names) (typeV::types)) body)
    termBuilder (Ctxt lvls names types) (Let fc name value body) | (Right (Res u typeV termV)) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Let fc name value body) | (Right (Res u typeV termV)) | (Right (Res lvlB typeB termBody))
      = pure (Res _ _ (Let termV termBody))

-- ### Sequencing

termBuilder ctxt (Seq left right) with (termBuilder ctxt left)
  termBuilder ctxt (Seq left right) | (Left err)
    = Left err

  termBuilder ctxt (Seq left right) | (Right (Res (IDX TERM) UnitTy termLeft)) with (termBuilder ctxt right)
    termBuilder ctxt (Seq left right) | (Right (Res (IDX TERM) UnitTy termLeft)) | (Left err)
      = Left err
    termBuilder ctxt (Seq left right) | (Right (Res (IDX TERM) UnitTy termLeft)) | (Right (Res (IDX level) type term))
      = pure (Res _ _ (Seq termLeft term))

    termBuilder ctxt (Seq left right) | (Right (Res (IDX TERM) UnitTy termLeft)) | (Right (Res u type _))
      = Left (WrongType NotATerm type)

  termBuilder ctxt (Seq left right) | (Right (Res u type _))
    = Left (WrongType NotAUnit type)

-- ## Derived tbd

-- [ End of Build ]



export
isTerm : (ast : AST)
             -> TermBuilder (SystemV Nil ModuleTy)
isTerm ast with (termBuilder (Ctxt Nil Nil Nil) ast)
  isTerm ast | (Left err)
    = Left err
  isTerm ast | (Right (Res _ (FuncTy UnitTy ModuleTy) term))
    = Right (App term MkUnit)
  isTerm ast | (Right (Res _ type term))

    = Left (TypeMismatch (FuncTy UnitTy ModuleTy) type)

-- --------------------------------------------------------------------- [ EOF ]
