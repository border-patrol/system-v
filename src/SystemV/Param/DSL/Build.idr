module SystemV.Param.DSL.Build

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

import        SystemV.Param.Types
import        SystemV.Param.Types.TYPE.Equality.DataTerms
import        SystemV.Param.Types.Views
import        SystemV.Param.Terms

import        SystemV.Param.DSL.AST
import public SystemV.Param.DSL.Error

import        SystemV.Param.DSL.Build.Helpers

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
termBuilder (Ctxt lvls names types) (TyVect fc size type)
  = do sres <- termBuilder (Ctxt lvls names types) size
       tres <- termBuilder (Ctxt lvls names types) type
       s <- isNat sres
       (D ty t) <- isData InVector tres
       pure (Res _ _ (TyVect s t))

-- ### Ports
termBuilder ctxt (TyPort fc type dir) with (termBuilder ctxt type)
  termBuilder ctxt (TyPort fc type dir) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (TyPort fc type dir) | (Right (Res (DATA TERM) typeT term))
    = pure (Res _ _ (TyPort term dir))

  termBuilder ctxt (TyPort fc type dir) | (Right (Res u typeT _))
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


-- ##
termBuilder ctxt (FuncDef fc name type def body) with (termBuilder ctxt type)
  termBuilder ctxt (FuncDef fc name type def body) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (FuncDef fc name type def body) | (Right tres) with (termBuilder ctxt def)
    termBuilder ctxt (FuncDef fc name type def body) | (Right tres) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) with (annDef tres dres)
      termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) | (Right (ANNDEF uty utm tyTy termTy tyTm termDef chk)) with (termBuilder (Ctxt (utm :: lvls) (MkName (Just name) utm :: names) (tyTm :: types)) body )
        termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) | (Right (ANNDEF uty utm tyTy termTy tyTm termDef chk)) | (Left err)
          = Left (Err fc err)
        termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) | (Right (ANNDEF uty utm tyTy termTy tyTm termDef chk)) | (Right bres) with (Helpers.bodyDef utm tyTm bres)
          termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) | (Right (ANNDEF uty utm tyTy termTy tyTm termDef chk)) | (Right bres) | (Left err)
            = Left err
          termBuilder (Ctxt lvls names types) (FuncDef fc name type def body) | (Right tres) | (Right dres) | (Right (ANNDEF uty utm tyTy termTy tyTm termDef chk)) | (Right bres) | (Right (BDef b vld))
            = Right (Res _ _ (FuncParam termTy termDef b vld chk))

termBuilder (Ctxt lvls names types) (AppOver func param)
  = do fres <- termBuilder (Ctxt lvls names types) func
       pres <- termBuilder (Ctxt lvls names types) param
       (APPOVER f p) <- appOver fres pres
       pure (Res _ _ (AppOver f p))

termBuilder (Ctxt lvls names types) (AppDef func)
  = do fres <- termBuilder (Ctxt lvls names types) func
       (FDef u a b f) <- isFuncDef fres
       pure (Res _ _ (AppDef f))



-- ## Modules \& Units \& Nats

termBuilder (Ctxt lvls names types) EndModule
  = pure (Res _ _ EndModule)

termBuilder (Ctxt lvls names types) UnitVal
  = pure (Res _ _ MkUnit)

-- ## Channels

-- ### Creation

termBuilder ctxt (MkChan fc type) with (termBuilder ctxt type)
  termBuilder ctxt (MkChan fc type) | (Left err)
    = Left (Err fc err)

  termBuilder ctxt (MkChan fc type) | (Right (Res (DATA TERM) typeT term))
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
  termBuilder (Ctxt lvls names types) (Drive fc port) | (Right res) with (isPortWithDir res OUT)
    termBuilder (Ctxt lvls names types) (Drive fc port) | (Right res) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Drive fc port) | (Right res) | (Right (MkDPair tyD term))
      = pure (Res _ _ (Drive term))

-- #### Catch
termBuilder ctxt (Catch fc port) with (termBuilder ctxt port)
  termBuilder ctxt (Catch fc port) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (Catch fc port) | (Right res) with (isPortWithDir res IN)
    termBuilder (Ctxt lvls names types) (Catch fc port) | (Right res) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Catch fc port) | (Right res) | (Right (MkDPair tyD term))
      = pure (Res _ _ (Catch term))

-- ## Operations on Ports

-- ### Casting
termBuilder ctxt (Cast fc port type dir) with (termBuilder ctxt port)
  termBuilder ctxt (Cast fc port type dir) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Cast fc port type dir) | (Right res) with (termBuilder ctxt type)
    termBuilder ctxt (Cast fc port type dir) | (Right resP) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Cast fc port type dir) | (Right resP) | (Right resT) with (canCast resP resT dir)
      termBuilder (Ctxt lvls names types) (Cast fc port type dir) | (Right resP) | (Right resT) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Cast fc port type dir) | (Right resP) | (Right resT) | (Right res) = Right res


-- ### Slicing
termBuilder ctxt (Slice fc port s e) with (termBuilder ctxt port)
  termBuilder ctxt (Slice fc port s e) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Slice fc port s e) | (Right pres) with (termBuilder ctxt s)
    termBuilder ctxt (Slice fc port s e) | (Right pres) | (Left err)
      = Left (Err fc err)
    termBuilder ctxt (Slice fc port s e) | (Right pres) | (Right sres) with (termBuilder ctxt e)
      termBuilder ctxt (Slice fc port s e) | (Right pres) | (Right sres) | (Left err)
        = Left (Err fc err)
      termBuilder (Ctxt lvls names types) (Slice fc port s e) | (Right pres) | (Right sres) | (Right eres)
        = do (PV ty dir p)  <- isPortVect pres
             s' <- isNat sres
             e' <- isNat eres
             pure (Res _ _ (Slice p s' e'))

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
      termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff)  with (conditionals res tt ff)
        termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff) | (Left err)
          = Left (Err fc err)
        termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff) | (Right (IFR cond x y))
          = Right (Res _ _ (IfThenElseR cond x y))
        termBuilder (Ctxt lvls names types) (IfThenElse fc test true false) | Right res | (Right tt) | (Right ff) | (Right (IFC cond x y))
          = Right (Res _ _ (IfThenElseC cond x y))


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

termBuilder ctxt (Index fc i port) with (termBuilder ctxt i)
  termBuilder ctxt (Index fc i port) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (Index fc i port) | (Right ires) with (termBuilder ctxt port)
    termBuilder ctxt (Index fc i port) | (Right ires) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (Index fc i port) | (Right ires) | (Right pres)
      = do i' <- isNat ires
           (PV ty dir p)  <- isPortVect pres
           pure (Res _ _ (Index i' p))

termBuilder ctxt (For fc n i port) with (termBuilder ctxt i)
  termBuilder ctxt (For fc n i port) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (For fc n i port) | (Right ires) with (termBuilder ctxt port)
    termBuilder ctxt (For fc n i port) | (Right ires) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (For fc n i port) | (Right ires) | (Right bres)
      = do (ForEach c b) <- index ires bres
           (Right (Res _ _ (For c b)))

termBuilder (Ctxt lvls names types) (TyNat fc) = pure (Res _ _ TyNat)
termBuilder (Ctxt lvls names types) (TyDATA fc) = pure (Res _ _ DATATYPE)
termBuilder (Ctxt lvls names types) (MkNat fc n) = pure (Res _ _ (MkNat n))
termBuilder (Ctxt lvls names types) (MkBool fc b) = pure (Res _ _ (MkBool b))

termBuilder ctxt (BoolNot fc expr) with (termBuilder ctxt expr)
  termBuilder ctxt (BoolNot fc expr) | (Left err)
    = Left (Err fc err)
  termBuilder (Ctxt lvls names types) (BoolNot fc expr) | (Right eres)
    = do e <- isBool eres
         pure (Res _ _ (BoolNot e))

termBuilder ctxt (NatOpCmp fc k l r) with (termBuilder ctxt l)
  termBuilder ctxt (NatOpCmp fc k l r) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (NatOpCmp fc k l r) | (Right lres) with (termBuilder ctxt r)
    termBuilder ctxt (NatOpCmp fc k l r) | (Right lres) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (NatOpCmp fc k l r) | (Right lres) | (Right rres)
      = do lop <- isNat lres
           rop <- isNat rres
           pure (Res _ _ (NatOpCmp k lop rop))

termBuilder ctxt (BoolOpBin fc k l r) with (termBuilder ctxt l)
  termBuilder ctxt (BoolOpBin fc k l r) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (BoolOpBin fc k l r) | (Right lres) with (termBuilder ctxt r)
    termBuilder ctxt (BoolOpBin fc k l r) | (Right lres) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (BoolOpBin fc k l r) | (Right lres) | (Right rres)
      = do lop <- isBool lres
           rop <- isBool rres
           pure (Res _ _ (BoolOpBin k lop rop))

termBuilder ctxt (NatOpArith fc k l r) with (termBuilder ctxt l)
  termBuilder ctxt (NatOpArith fc k l r) | (Left err)
    = Left (Err fc err)
  termBuilder ctxt (NatOpArith fc k l r) | (Right lres) with (termBuilder ctxt r)
    termBuilder ctxt (NatOpArith fc k l r) | (Right lres) | (Left err)
      = Left (Err fc err)
    termBuilder (Ctxt lvls names types) (NatOpArith fc k l r) | (Right lres) | (Right rres)
      = do lop <- isNat lres
           rop <- isNat rres
           pure (Res _ _ (NatOpArith k lop rop))

-- [ End of Build ]


namespace Param
  export
  build : (ast : AST)
               -> Either Param.Error (SystemV Nil ModuleTy)
  build ast with (termBuilder (Ctxt Nil Nil Nil) ast)
    build ast | (Left err)
      = Left err
    build ast | (Right (Res _ (FuncTy UnitTy ModuleTy) term))
      = Right (App term MkUnit)
    build ast | (Right (Res _ type term))

      = Left (TypeMismatch (FuncTy UnitTy ModuleTy) type)

-- --------------------------------------------------------------------- [ EOF ]
