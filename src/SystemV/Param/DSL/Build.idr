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
termBuilder (Ctxt lvls names types) (TyPort fc type dir)
  = do tres <- termBuilder (Ctxt lvls names types) type
       (D ty t) <- isData InVector tres
       pure (Res _ _ (TyPort t dir))

-- ## STLC

-- ### References
termBuilder (Ctxt lvls names types) (Ref name) with (isName (get name) names)
  termBuilder (Ctxt lvls names types) (Ref name) | (Yes (MkDPair level idx_name)) with (mkVar idx_name types)
    termBuilder (Ctxt lvls names types) (Ref name) | (Yes (MkDPair level idx_name)) | (MkDPair type idx)
      = pure (Res _ _ (Var idx))
  termBuilder (Ctxt lvls names types) (Ref name) | (No contra)
    = Left (Err (span name) (NotAName (get name)))

-- ### Functions
termBuilder (Ctxt lvls names types) (Func fc name type body)
  = do tres <- termBuilder (Ctxt lvls names types) type

       ANN meta t termPa chk <- annotation tres

       bres <- termBuilder (Ctxt (IDX TERM :: lvls) (MkName (Just name) (IDX TERM) :: names) (termPa :: types)) body

       B b vld <- Helpers.body termPa bres

       pure (Res _ _ (Func t b chk vld))

-- ### Application
termBuilder (Ctxt lvls names types) (App func param)
  = do fres <- termBuilder (Ctxt lvls names types) func
       pres <- termBuilder (Ctxt lvls names types) param

       APP f a <- application fres pres

       pure (Res _ _ (App f a))


-- ## Func Def
termBuilder (Ctxt lvls names types) (FuncDef fc name type def body)
  = do tres <- termBuilder (Ctxt lvls names types) type
       dres <- termBuilder (Ctxt lvls names types) def

       ANNDEF uty utm tyTy termTy tyTm termDef chk <- annDef tres dres

       bres <- termBuilder (Ctxt (utm :: lvls) (MkName (Just name) utm :: names) (tyTm :: types)) body
       BDef b vld <- Helpers.bodyDef utm tyTm bres
       pure (Res _ _ (FuncParam termTy termDef b vld chk))

-- ## AppOver

termBuilder (Ctxt lvls names types) (AppOver func param)
  = do fres <- termBuilder (Ctxt lvls names types) func
       pres <- termBuilder (Ctxt lvls names types) param
       (APPOVER f p) <- appOver fres pres
       pure (Res _ _ (AppOver f p))

-- ## AppDef
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

termBuilder  (Ctxt lvls names types) (MkChan fc type)
  = do tres <- termBuilder (Ctxt lvls names types) type
       (D ty t) <- isData InChan tres
       pure (Res _ _ (MkChan t))


-- ### Projection

-- #### Write To
termBuilder  (Ctxt lvls names types) (WriteTo fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan cres
       pure (Res _ _ (WriteTo (snd c)))

-- #### Read To
termBuilder  (Ctxt lvls names types) (ReadFrom fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan cres
       pure (Res _ _ (ReadFrom (snd c)))

-- ### Driving

-- #### Drive

termBuilder (Ctxt lvls names types) (Drive fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       MkDPair ty p <- isPortWithDir pres OUT
       pure (Res _ _ (Drive p))

-- #### Catch
termBuilder (Ctxt lvls names types) (Catch fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       MkDPair ty p <- isPortWithDir pres IN
       pure (Res _ _ (Catch p))

-- ## Operations on Ports

-- ### Casting
termBuilder (Ctxt lvls names types) (Cast fc port type dir)
  = do pres <- termBuilder (Ctxt lvls names types) port
       tres <- termBuilder (Ctxt lvls names types) type
       canCast pres tres dir

-- ### Slicing
termBuilder (Ctxt lvls names types) (Slice fc port start end)
  = do pres <- termBuilder (Ctxt lvls names types) port
       sres <- termBuilder (Ctxt lvls names types) start
       eres <- termBuilder (Ctxt lvls names types) end
       (PV ty dir p)  <- isPortVect pres
       s <- isNat sres
       e <- isNat eres
       pure (Res _ _ (Slice p s e))

-- ### Conditionals

termBuilder (Ctxt lvls names types) (IfThenElse fc test true false)
  = do cres <- termBuilder (Ctxt lvls names types) test
       tres <- termBuilder (Ctxt lvls names types) true
       fres <- termBuilder (Ctxt lvls names types) false
       IFR c t f <- conditionals cres tres fres
           | IFC c t f => pure (Res _ _ (IfThenElseC c t f))

       pure (Res _ _ (IfThenElseR c t f))

-- ### Connecting Ports
termBuilder (Ctxt lvls names types) (Connect fc portL portR)
  = do lres <- termBuilder (Ctxt lvls names types) portL
       rres <- termBuilder (Ctxt lvls names types) portR

       CP l r prf <- connectPorts lres rres
       pure (Res _ _ (Connect l r prf))


-- ## Gates
-- ### Not
termBuilder (Ctxt lvls names types) (NotGate fc portOut portIn)
  = do ores <- termBuilder (Ctxt lvls names types) portOut
       ires <- termBuilder (Ctxt lvls names types) portIn

       NP pout pin <- notGatePorts ores ires
       pure (Res _ _ (Not pout pin))

-- ### Bin Gate

termBuilder (Ctxt lvls names types) (Gate fc kind portOut portInA portInB)
  = do po  <- termBuilder (Ctxt lvls names types) portOut
       pia <- termBuilder (Ctxt lvls names types) portInA
       pib <- termBuilder (Ctxt lvls names types) portInB

       BP pout pinA pinB <- binGatePorts po pia pib

       pure (Res _ _ (Gate kind pout pinA pinB))

-- ### Let binding
termBuilder (Ctxt lvls names types) (Let fc name value body)
  = do (Res u tyV v) <- termBuilder (Ctxt lvls names types) value
       (Res _ _   b) <- termBuilder (Ctxt (u::lvls) ((MkName (Just name) u)::names) (tyV::types)) body
       pure (Res _ _ (Let v b))

-- ### Sequencing

termBuilder (Ctxt lvls names types) (Seq left right)
  = do lres <- termBuilder (Ctxt lvls names types) left
       l    <- isUnit lres
       rres <- termBuilder (Ctxt lvls names types) right
       (T ty r) <- isTerm rres
       pure (Res _ _ (Seq l r))

-- ## Indicies

termBuilder (Ctxt lvls names types) (Index fc i port)
  = do ires <- termBuilder (Ctxt lvls names types) i
       pres <- termBuilder (Ctxt lvls names types) port
       i' <- isNat ires
       (PV ty dir p)  <- isPortVect pres
       pure (Res _ _ (Index i' p))

termBuilder (Ctxt lvls names types) (For fc n i port)
  = do ires <- termBuilder (Ctxt lvls names types) i
       pres <- termBuilder (Ctxt lvls names types) port
       (ForEach c b) <- foreach ires pres
       pure (Res _ _ (For c b))

termBuilder (Ctxt lvls names types) (TyNat fc) = pure (Res _ _ TyNat)
termBuilder (Ctxt lvls names types) (TyDATA fc) = pure (Res _ _ DATATYPE)
termBuilder (Ctxt lvls names types) (MkNat fc n) = pure (Res _ _ (MkNat n))
termBuilder (Ctxt lvls names types) (MkBool fc b) = pure (Res _ _ (MkBool b))

termBuilder (Ctxt lvls names types) (BoolNot fc expr)
  = do eres <- termBuilder (Ctxt lvls names types) expr
       e <- isBool eres
       pure (Res _ _ (BoolNot e))

termBuilder (Ctxt lvls names types) (NatOpCmp fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isNat lres
       rop <- isNat rres
       pure (Res _ _ (NatOpCmp k lop rop))

termBuilder (Ctxt lvls names types) (BoolOpBin fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isBool lres
       rop <- isBool rres
       pure (Res _ _ (BoolOpBin k lop rop))

termBuilder (Ctxt lvls names types) (NatOpArith fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isNat lres
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
