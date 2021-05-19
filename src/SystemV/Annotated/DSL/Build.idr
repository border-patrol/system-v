module SystemV.Annotated.DSL.Build

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

import public SystemV.Common.Builder

import        SystemV.Annotated.Types
import        SystemV.Annotated.Types.Views
import        SystemV.Annotated.Terms

import        SystemV.Annotated.DSL.AST
import public SystemV.Annotated.DSL.Error

import        SystemV.Annotated.DSL.Build.Helpers

%hide Data.Nat.pred -- shadowing

%default total


termBuilder : (ctxt : Context TYPE lvls types)
           -> (ast  : AST)
                   -> TermBuilder (Result TYPE SystemV lvls types)
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

-- ### Ports
termBuilder ctxt (TyPort fc type dir s i) with (termBuilder ctxt type)
  termBuilder ctxt (TyPort fc type dir s i) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (TyPort fc type dir s i) | (Right (Res (DATA TYPE) typeT term))
    = pure (Res _ _ (TyPort term dir s i))

  termBuilder ctxt (TyPort fc type dir s i) | (Right (Res u typeT _))
    = Left (Err fc (WrongType (NotADataType InPort) typeT))

-- ## STLC

-- ### References
termBuilder (Ctxt lvls names types) (Ref name) with (isName (get name) names)
  termBuilder (Ctxt lvls names types) (Ref name) | (Yes (MkDPair level idx_name)) with (mkVar idx_name types)
    termBuilder (Ctxt lvls names types) (Ref name) | (Yes (MkDPair level idx_name)) | (MkDPair type idx)
      = pure (Res _ _ (Var idx))
  termBuilder (Ctxt lvls names types) (Ref name) | (No contra)
    = Left (Err (span name) (NotAName (get name)))

-- ### Functions
termBuilder ctxt (Func fc name type body) with (termBuilder ctxt type)
  termBuilder ctxt (Func fc name type body) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) with (annotation tres)
    termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) | (Right (ANN meta termTy termPa chk)) with (termBuilder (Ctxt (IDX TERM :: lvls) (MkName (Just name) (IDX TERM) :: names) (termPa :: types)) body)
      termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) | (Right (ANN meta termTy termPa chk)) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) | (Right (ANN meta termTy termPa chk)) | (Right bres) with (Helpers.body termPa bres)
        termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) | (Right (ANN meta termTy termPa chk)) | (Right bres) | (Left err)
          = Left (Err fc err)
        termBuilder (Ctxt lvls names types) (Func fc name type body) | (Right tres) | (Right (ANN meta termTy termPa chk)) | (Right bres) | (Right (B termBody vld))
          = Right (Res _ _ (Func termTy termBody chk vld))

-- ### Application
termBuilder ctxt (App func param) with (termBuilder ctxt func)
  termBuilder ctxt (App func param) | (Left err)
    = Left err
  termBuilder ctxt (App func param) | (Right fres) with (termBuilder ctxt param)
    termBuilder ctxt (App func param) | (Right fres) | (Left err)
      = Left err
    termBuilder (Ctxt lvls names types) (App func param) | (Right fres) | (Right pres) with (application fres pres)
      termBuilder (Ctxt lvls names types) (App func param) | (Right fres) | (Right pres) | (Left err)
        = Left err
      termBuilder (Ctxt lvls names types) (App func param) | (Right fres) | (Right pres) | (Right (APP f a))
        = Right (Res _ _ (App f a))


-- ## Modules \& Units \& Nats

termBuilder (Ctxt lvls names types) EndModule
  = pure (Res _ _ EndModule)

termBuilder (Ctxt lvls names types) UnitVal
  = pure (Res _ _ MkUnit)

-- ## Channels

-- ### Creation

termBuilder ctxt (MkChan fc type s i) with (termBuilder ctxt type)
  termBuilder ctxt (MkChan fc type s i) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (MkChan fc type s i) | (Right (Res (DATA TYPE) typeT term))
    = pure (Res _ _ (MkChan term s i))

  termBuilder ctxt (MkChan fc type s i) | (Right (Res u typeT _))
    = Left (Err fc (WrongType (NotADataType InChan) typeT))

-- ### Projection

-- #### Write To
termBuilder ctxt (WriteTo fc chan) with (termBuilder ctxt chan)
  termBuilder ctxt (WriteTo fc chan) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (WriteTo fc chan) | (Right (Res (IDX TERM) (ChanTy typeT s i) term))
    = pure (Res _ _ (WriteTo term))

  termBuilder ctxt (WriteTo fc chan) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAChannel typeT))

-- #### Read To
termBuilder ctxt (ReadFrom fc chan) with (termBuilder ctxt chan)
  termBuilder ctxt (ReadFrom fc chan) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (ReadFrom fc chan) | (Right (Res (IDX TERM) (ChanTy typeT s i) term))
    = pure (Res _ _ (ReadFrom term))

  termBuilder ctxt (ReadFrom fc chan) | (Right (Res u typeT _))
    = Left (Err fc (WrongType NotAChannel typeT))

-- ### Driving

-- #### Drive

termBuilder ctxt (Drive fc s i port) with (termBuilder ctxt port)
  termBuilder ctxt (Drive fc s i port) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Drive fc s i port) | (Right res) with (isPortAttr res OUT s i)
    termBuilder (Ctxt lvls names types) (Drive fc s i port) | (Right res) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Drive fc s i port) | (Right res) | (Right (Pa tyD term))
      = pure (Res _ _ (Drive s i term))

-- #### Catch
termBuilder ctxt (Catch fc port) with (termBuilder ctxt port)
  termBuilder ctxt (Catch fc port) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Catch fc port) | (Right res) with (isPortWithDir res IN)
    termBuilder (Ctxt lvls names types) (Catch fc port) | (Right res) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Catch fc port) | (Right res) | (Right (i ** s ** tyD ** term))
      = pure (Res _ _ (Catch term))

-- ## Operations on Ports

-- ### Casting
termBuilder ctxt (Cast fc port type dir s i) with (termBuilder ctxt port)
  termBuilder ctxt (Cast fc port type dir s i) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Cast fc port type dir s i) | (Right res) with (termBuilder ctxt type)
    termBuilder ctxt (Cast fc port type dir s i) | (Right resP) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Cast fc port type dir s i) | (Right resP) | (Right resT) with (canCast resP resT dir s i)
      termBuilder (Ctxt lvls names types) (Cast fc port type dir s i) | (Right resP) | (Right resT) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Cast fc port type dir s i) | (Right resP) | (Right resT) | (Right res) = Right res


-- ### Slicing
termBuilder ctxt (Slice fc port s e) with (termBuilder ctxt port)
  termBuilder ctxt (Slice fc port s e) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Slice fc port s e) | (Right res) with (isPortVect res)
    termBuilder (Ctxt lvls names types) (Slice fc port s e) | (Right res) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Slice fc port s e) | (Right res) | (Right (PV x term)) with (validBound s e x)
      termBuilder (Ctxt lvls names types) (Slice fc port s e) | (Right res) | (Right (PV x term)) | (Yes prfWhy)
        = pure (Res _ _ (Slice term s e prfWhy))
      termBuilder (Ctxt lvls names types) (Slice fc port s e) | (Right res) | (Right (PV x term)) | (No msgWhyNot prfWhyNot)
        = Left (Err fc (InvalidBound msgWhyNot))

-- ### Conditionals

termBuilder ctxt (IfThenElse fc test true false) with (termBuilder ctxt test)
  termBuilder ctxt (IfThenElse fc test true false) | Left err
    = Left (Err fc err)
  termBuilder ctxt (IfThenElse fc test true false) | Right res with (termBuilder ctxt true)
    termBuilder ctxt (IfThenElse fc test true false) | Right res | (Left err)
      = Left (Err fc err)
    termBuilder ctxt (IfThenElse fc test true false) | Right res | (Right tt) with (termBuilder ctxt false)
      termBuilder ctxt (IfThenElse fc test true false) | Right res | (Right tt) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff) with (conditionals res tt ff)
        termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff) | (Left err)
          = Left (Err fc err)
        termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff) | (Right (IF cond x y))
          = Right (Res _ _ (IfThenElseR cond x y))

-- ### Connecting Ports
termBuilder ctxt (Connect fc portL portR) with (termBuilder ctxt portL)
  termBuilder ctxt (Connect fc portL portR) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Connect fc portL portR) | (Right resL) with (termBuilder ctxt portR)
    termBuilder ctxt (Connect fc portL portR) | (Right resL) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Connect fc portL portR) | (Right resL) | (Right resR) with (connectPorts resL resR)
      termBuilder (Ctxt lvls names types) (Connect fc portL portR) | (Right resL) | (Right resR) | Left err
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Connect fc portL portR) | (Right resL) | (Right resR) | Right (CP pA pB prf)
        = Right (Res _ _ (Connect pA pB prf))


-- ## Gates
-- ### Not
termBuilder ctxt (NotGate fc portOut portIn) with (termBuilder ctxt portOut)
  termBuilder ctxt (NotGate fc portOut portIn) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (NotGate fc portOut portIn) | (Right pout) with (termBuilder ctxt portIn)
    termBuilder ctxt (NotGate fc portOut portIn) | (Right pout) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (NotGate fc portOut portIn) | (Right poutR) | (Right pinR) with (notGatePorts poutR pinR)
      termBuilder (Ctxt lvls names types) (NotGate fc portOut portIn) | (Right poutR) | (Right pinR) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (NotGate fc portOut portIn) | (Right poutR) | (Right pinR) | (Right (NP pout pin))
        = Right (Res _ _ (Not pout pin))

-- ### Bin Gate

termBuilder ctxt (Gate fc kind portOut portInA portInB) with (termBuilder ctxt portOut)
  termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right po) with (termBuilder ctxt portInA)
    termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right po) | (Left err)
      = Left (Err fc err)
    termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right po) | (Right pia) with (termBuilder ctxt portInB)
      termBuilder ctxt (Gate fc kind portOut portInA portInB) | (Right po) | (Right pia) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Gate fc kind portOut portInA portInB) | (Right po) | (Right pia) | (Right pib) with (binGatePorts po pia pib)
        termBuilder (Ctxt lvls names types) (Gate fc kind portOut portInA portInB) | (Right po) | (Right pia) | (Right pib) | (Left err)
          = Left (Err fc err)
        termBuilder (Ctxt lvls names types) (Gate fc kind portOut portInA portInB) | (Right po) | (Right pia) | (Right pib) | (Right (BP pout pinA pinB))
          = Right (Res _ _ (Gate kind pout pinA pinB))
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
  termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) with (isUnit res)
    termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) | Left err
      = Left err
    termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) | Right lunit with (termBuilder (Ctxt lvls names types) right)
      termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) | Right lunit | (Left err)
        = Left err
      termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) | Right lunit | (Right resR) with (isTerm resR)
        termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) | Right lunit | (Right resR) | (Left err)
          = Left err
        termBuilder (Ctxt lvls names types) (Seq left right) | (Right res) | Right lunit | (Right resR) | (Right (T ty term))
          = Right (Res _ _ (Seq lunit term))

-- ## Indicies

termBuilder ctxt (Index fc i port) with (termBuilder ctxt port)
    termBuilder ctxt (Index fc i port) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Index fc i port) | (Right res) with (isPortVect res)
      termBuilder (Ctxt lvls names types) (Index fc i port) | (Right res) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Index fc i port) | (Right res) | (Right (PV s term)) with (isLTE (S i) s)
        termBuilder (Ctxt lvls names types) (Index fc i port) | (Right res) | (Right (PV s term)) | (Yes prf)
          = Right (Res _ _ (Index i term prf))
        termBuilder (Ctxt lvls names types) (Index fc i port) | (Right res) | (Right (PV s term)) | (No contra)
          = Left (Err fc (IndexOutOfBounds i s))

-- [ End of Build ]

namespace Annotated
  export
  build : (ast : AST)
               -> Either Annotated.Error (SystemV Nil ModuleTy)
  build ast with (termBuilder (Ctxt Nil Nil Nil) ast)
    build ast | (Left err)
      = Left err
    build ast | (Right (Res _ (FuncTy UnitTy ModuleTy) term))
      = Right (App term MkUnit)
    build ast | (Right (Res _ type term))

      = Left (TypeMismatch (FuncTy UnitTy ModuleTy) type)

-- --------------------------------------------------------------------- [ EOF ]
