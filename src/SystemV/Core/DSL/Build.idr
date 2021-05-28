module SystemV.Core.DSL.Build

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

import        SystemV.Core.Types
import        SystemV.Core.Types.Views
import        SystemV.Core.Terms

import        SystemV.Core.DSL.AST
import public SystemV.Core.DSL.Error

import        SystemV.Core.DSL.Build.Helpers

%hide Data.Nat.pred -- shadowing

%default total


termBuilder : (ctxt : Context TYPE lvls types)
           -> (ast  : AST)
                   -> TermBuilder (Result TYPE SystemV lvls types)
-- ## Types

-- ### Unit
termBuilder (Ctxt lvls names types) (TyUnit fc)
  = pure (Res _ _ TyUnit)

-- ### Logic
termBuilder (Ctxt lvls names types) (TyLogic fc)
  = pure (Res _ _ TyLogic)

-- ### Vectors
termBuilder (Ctxt lvls names types) (TyVect fc size type) with (isWhole size)

-- Right size
  termBuilder (Ctxt lvls names types) (TyVect fc (S n) type) | (Yes YesIsWhole) =
    do tres <- termBuilder (Ctxt lvls names types) type

       (D ty t) <- isData fc InVector tres

       pure (Res _ _ (TyVect (W (S n) ItIsSucc) t))

-- Has Size Zero
  termBuilder (Ctxt lvls names types) (TyVect fc size type) | (No contra)
    = Left (Err fc VectorSizeZero)

-- ### Ports
termBuilder (Ctxt lvls names types) (TyPort fc type dir)
  = do tres <- termBuilder (Ctxt lvls names types) type
       (D ty t) <- isData (getFC type) InVector tres
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

       (TT tyType termType) <- isType (getFC type) tres

       case synthesis tyType of
         No msgWhyNot prfWhyNot =>
           Left (Err fc (InvalidFuncSynth msgWhyNot tyType))

         Yes (MkDPair argty (Synth argty prfarg prfret chk)) =>

           do bres <- termBuilder (Ctxt (IDX TERM :: lvls)
                                        (MkName (Just name) (IDX TERM) :: names)
                                        (argty :: types)) body
              (TTerm tyBody termBody) <- isTermTerm (getFC body) bres

              case Function.validTerm (IDX TERM) (FuncTy argty tyBody) of
                No msgWhyNot prfWhyNot =>
                  (Left (Err fc (InvalidFunc msgWhyNot argty tyBody)))

                Yes prfWhy =>
                  pure (Res _ _ (Func termType termBody chk prfWhy))


-- ### Application
termBuilder (Ctxt lvls names types) (App fc func param)
  = do fres <- termBuilder (Ctxt lvls names types) func
       pres <- termBuilder (Ctxt lvls names types) param

       (F     tyA  tyB f) <- isFunc     (getFC func)  fres
       (TTerm tyA'     a) <- isTermTerm (getFC param) pres

       case TypeTerms.decEq tyA tyA' of
         (Yes (Same Refl Refl)) =>
           pure (Res _ _ (App f a))

         (No msgWhyNot prfWhyNot) =>
           Left (Err (getFC param) (TypeMismatch tyA tyA'))

-- ## Modules \& Units \& Nats

termBuilder (Ctxt lvls names types) (EndModule _)
  = pure (Res _ _ EndModule)

termBuilder (Ctxt lvls names types) (UnitVal _)
  = pure (Res _ _ MkUnit)

-- ## Channels

-- ### Creation

termBuilder  (Ctxt lvls names types) (MkChan fc type)
  = do tres <- termBuilder (Ctxt lvls names types) type
       (D ty t) <- isData (getFC type) InChan tres
       pure (Res _ _ (MkChan t))

-- ### Projection

-- #### Write To
termBuilder  (Ctxt lvls names types) (WriteTo fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan (getFC chan) cres
       pure (Res _ _ (WriteTo (snd c)))

-- #### Read To
termBuilder  (Ctxt lvls names types) (ReadFrom fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan (getFC chan) cres
       pure (Res _ _ (ReadFrom (snd c)))

-- ### Driving

-- #### Drive

termBuilder (Ctxt lvls names types) (Drive fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       MkDPair ty p <- isPortWithDir (getFC port) pres OUT
       pure (Res _ _ (Drive p))

-- #### Catch
termBuilder (Ctxt lvls names types) (Catch fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       MkDPair ty p <- isPortWithDir (getFC port) pres IN
       pure (Res _ _ (Catch p))

-- ## Operations on Ports


-- ### Casting
termBuilder (Ctxt lvls names types) (Cast fc port type toDir)
  = do pres <- termBuilder (Ctxt lvls names types) port
       tres <- termBuilder (Ctxt lvls names types) type

       (P fromDir fromTy from) <- isPort (getFC port) pres
       (D toDTy data_) <- isData (getFC type) InCast tres

       let fromP = PortTy fromTy fromDir
       let toP   = PortTy toDTy  toDir

       case validCast (PortTy fromTy fromDir) (PortTy toDTy toDir) of
         (Yes prfWhy)             => Right (Res _ _ (Cast from prfWhy))
         (No msgWhyNot prfWhyNot) => Left (Err fc (InvalidCast msgWhyNot fromP toP))

-- ### Slicing
termBuilder (Ctxt lvls names types) (Slice fc port a o)
  = do pres <- termBuilder (Ctxt lvls names types) port
       (PV s p)  <- isPortVect (getFC port) pres

       case validBound a o s of
          Yes prfWhy => pure (Res _ _ (Slice p a o prfWhy))
          No msgWhyNot prfWhyNot => Left (Err fc (InvalidBound msgWhyNot))

-- ### Conditionals

termBuilder (Ctxt lvls names types) (IfThenElse fc test true false)
  = do cres <- termBuilder (Ctxt lvls names types) test
       tres <- termBuilder (Ctxt lvls names types) true
       fres <- termBuilder (Ctxt lvls names types) false

       (tyD ** cc) <- isPortWithDir (getFC test) cres IN
       t  <- isUnit (getFC true)  tres
       f  <- isUnit (getFC false) fres

       pure (Res _ _ (IfThenElseR cc t f))

-- ### Connecting Ports
termBuilder (Ctxt lvls names types) (Connect fc portL portR)
  = do lres <- termBuilder (Ctxt lvls names types) portL
       rres <- termBuilder (Ctxt lvls names types) portR

       (P da ta l) <- isPort (getFC portL) lres
       (P db tb r) <- isPort (getFC portR) rres

       let ptA = PortTy ta da
       let ptB = PortTy tb db

       case DataTypes.decEq ta tb of
         (Yes (Same Refl Refl)) =>
           case validFlow da db of
             (Yes prf) => pure (Res _ _ (Connect l r prf))

             (No msgWhyNot prfWhyNot) =>
               Left (Err fc (InvalidFlow msgWhyNot))
         (No msgWhyNot prfWhyNot) =>
           Left (Err fc (TypeMismatch ptA ptB))

-- ## Gates
-- ### Not
termBuilder (Ctxt lvls names types) (NotGate fc portOut portIn)
  = do ores <- termBuilder (Ctxt lvls names types) portOut
       ires <- termBuilder (Ctxt lvls names types) portIn

       (to ** output) <- isPortWithDir (getFC portOut) ores OUT
       (ti ** input)  <- isPortWithDir (getFC portIn) ires  IN

       let po = PortTy to OUT
       let pi = PortTy ti IN

       case DataTypes.decEq to ti of
         Yes (Same Refl Refl) =>
           pure (Res _ _ (Not output input))

         No msgWhyNot prfWhyNot =>
           Left (Err fc (TypeMismatch to ti))

-- ### Bin Gate

termBuilder (Ctxt lvls names types) (Gate fc kind portOut portInA portInB)
  = do ores  <- termBuilder (Ctxt lvls names types) portOut
       ares <- termBuilder (Ctxt lvls names types) portInA
       bres <- termBuilder (Ctxt lvls names types) portInB

       (to ** output) <- isPortWithDir (getFC portOut) ores OUT
       (ta ** inputA) <- isPortWithDir (getFC portInA) ares IN
       (tb ** inputB) <- isPortWithDir (getFC portInB) bres IN

       let po = PortTy to OUT
       let pa = PortTy ta IN
       let pb = PortTy tb IN

       case allDataEqual to ta tb of
         No AB contra => Left (Err fc (TypeMismatch to ta))
         No AC contra => Left (Err fc (TypeMismatch to tb))
         Yes ADE      => pure (Res _ _ (Gate kind output inputA inputB))

-- ### Let binding
termBuilder (Ctxt lvls names types) (Let fc name value body)
  = do (Res u tyV v) <- termBuilder (Ctxt lvls names types) value
       (Res _ _   b) <- termBuilder (Ctxt (u::lvls) ((MkName (Just name) u)::names) (tyV::types)) body
       pure (Res _ _ (Let v b))

-- ### Sequencing
termBuilder (Ctxt lvls names types) (Seq fc left right)
  = do lres <- termBuilder (Ctxt lvls names types) left
       l    <- isUnit (getFC left) lres

       rres <- termBuilder (Ctxt lvls names types) right

       (T ty r) <- isTerm (getFC right) rres

       pure (Res _ _ (Seq l r))

-- ## Indicies

termBuilder (Ctxt lvls names types) (Index fc i port)
  = do tres <- termBuilder (Ctxt lvls names types) port

       (PV s t) <- isPortVect (getFC port) tres

       case isLTE (S i) s of
         Yes prf => Right (Res _ _ (Index i t prf))
         No contra => Left (Err fc (IndexOutOfBounds i s))

-- [ End of Build ]


namespace Core
  export
  build : (ast : AST)
               -> Either Core.Error (SystemV Nil ModuleTy)
  build ast with (termBuilder (Ctxt Nil Nil Nil) ast)
    build ast | (Left err)
      = Left err
    build ast | (Right (Res _ (FuncTy UnitTy ModuleTy) term))
      = Right (App term MkUnit)
    build ast | (Right (Res _ type term))

      = Left (TypeMismatch (FuncTy UnitTy ModuleTy) type)

-- --------------------------------------------------------------------- [ EOF ]
