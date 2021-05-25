module SystemV.HigherOrder.DSL.Build

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

import        SystemV.HigherOrder.Types

import        SystemV.Core.Types.Views

import        SystemV.HigherOrder.Terms

import        SystemV.HigherOrder.DSL.AST
import public SystemV.HigherOrder.DSL.Error

import        SystemV.HigherOrder.DSL.Build.Helpers

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

-- ### Module
termBuilder (Ctxt lvls names types) TyModule
  = pure (Res _ _ TyModule)

-- ### Function
termBuilder (Ctxt lvls names types) (TyFunc fc name a b)
  = do ares <- termBuilder (Ctxt lvls names types) a
       bres <- termBuilder (Ctxt lvls names types) b
       TF tyP tyR prf <- typeFunc ares bres
       pure (Res _ _ (TyFunc tyP tyR prf))

-- ### Vectors
termBuilder (Ctxt lvls names types) (TyVect fc size type) with (isWhole size)

-- Right size
  termBuilder (Ctxt lvls names types) (TyVect fc (S n) type) | (Yes YesIsWhole) =
    do tres <- termBuilder (Ctxt lvls names types) type

       (D ty t) <- isData InVector tres

       pure (Res _ _ (TyVect (W (S n) ItIsSucc) t))

-- Has Size Zero
  termBuilder (Ctxt lvls names types) (TyVect fc size type) | (No contra)
    = Left (Err fc VectorSizeZero)

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
termBuilder (Ctxt lvls names types) (Slice fc port a o)
  = do pres <- termBuilder (Ctxt lvls names types) port
       (PV s p)  <- isPortVect pres

       case validBound a o s of
          Yes prfWhy => pure (Res _ _ (Slice p a o prfWhy))
          No msgWhyNot prfWhyNot => Left (Err fc (InvalidBound msgWhyNot))


-- ### Conditionals

termBuilder (Ctxt lvls names types) (IfThenElse fc test true false)
  = do cres <- termBuilder (Ctxt lvls names types) test
       tres <- termBuilder (Ctxt lvls names types) true
       fres <- termBuilder (Ctxt lvls names types) false
       IF c t f <- conditionals cres tres fres

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
  = do tres <- termBuilder (Ctxt lvls names types) port
       (PV s t) <- isPortVect tres
       case isLTE (S i) s of
         Yes prf => Right (Res _ _ (Index i t prf))
         No contra => Left (Err fc (IndexOutOfBounds i s))

-- [ End of Build ]

namespace HigherOrder
  export
  build : (ast : AST)
               -> Either HigherOrder.Error (SystemV Nil ModuleTy)
  build ast with (termBuilder (Ctxt Nil Nil Nil) ast)
    build ast | (Left err)
      = Left err
    build ast | (Right (Res _ (FuncTy UnitTy ModuleTy) term))
      = Right (App term MkUnit)
    build ast | (Right (Res _ type term))

      = Left (TypeMismatch (FuncTy UnitTy ModuleTy) type)

-- --------------------------------------------------------------------- [ EOF ]
