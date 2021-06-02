module SystemV.Params.DSL.Build

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

import        SystemV.Params.Types
import        SystemV.Params.Types.TYPE.Equality.DataTerms
import        SystemV.Params.Types.Views
import        SystemV.Params.Terms

import        SystemV.Params.DSL.AST
import public SystemV.Params.DSL.Error

import        SystemV.Params.DSL.Build.Helpers

%hide Data.Nat.pred -- shadowing

%default total


termBuilder : (ctxt : Context TYPE lvls types)
           -> (ast  : AST)
                   -> TermBuilder (Result TYPE SystemV lvls types)
-- ## Types

-- ### Unit
termBuilder (Ctxt lvls names types) (TyUnit fc)
  = pure (Res _ _ (TyUnit fc))

-- ### Logic
termBuilder (Ctxt lvls names types) (TyLogic fc)
  = pure (Res _ _ (TyLogic fc))

-- ### Vectors
termBuilder (Ctxt lvls names types) (TyVect fc size type)
  = do sres <- termBuilder (Ctxt lvls names types) size
       tres <- termBuilder (Ctxt lvls names types) type
       s <- isNat (getFC size) sres
       t <- isData (getFC type) InVector tres
       pure (Res _ _ (TyVect fc s t))

-- ### Ports
termBuilder (Ctxt lvls names types) (TyPort fc type dir)
  = do tres <- termBuilder (Ctxt lvls names types) type
       t    <- isData (getFC type) InVector tres
       pure (Res _ _ (TyPort fc t dir))

-- ## STLC

-- ### References
termBuilder (Ctxt lvls names types) (Ref name) with (isName (get name) names)
  termBuilder (Ctxt lvls names types) (Ref name) | (Yes (MkDPair level idx_name)) with (mkVar idx_name types)
    termBuilder (Ctxt lvls names types) (Ref name) | (Yes (MkDPair level idx_name)) | (MkDPair type idx)
      = pure (Res _ _ (Var (span name) idx))
  termBuilder (Ctxt lvls names types) (Ref name) | (No contra)
    = Left (Err (span name) (NotAName (get name)))

-- ### Functions
termBuilder (Ctxt lvls names types) (Func fc name type body)
  = do tres <- termBuilder (Ctxt lvls names types) type

       (TT tyP termP) <- isType (getFC type) tres
       case synthesis tyP of
         No msgWhyNot prfWhyNot =>
           Left (Err fc (InvalidFuncSynth msgWhyNot tyP))

         Yes (MkDPair argty (Synth argty prfarg prfret chk)) =>
           do bres <- termBuilder (Ctxt (IDX TERM :: lvls)
                                        (MkName (Just name) (IDX TERM) :: names)
                                        (argty :: types)) body

              (TTerm tyB termB) <- isTermTerm (getFC body) bres

              case Function.validTerm (IDX TERM) (FuncTy argty tyB) of
                Yes prfWhy =>
                  Right (Res _ _ (Func fc termP termB chk prfWhy))
                No msgWhyNot prfWhyNot =>
                  Left (Err fc (InvalidFunc msgWhyNot argty tyB))


-- ### Application
termBuilder (Ctxt lvls names types) (App fc func param)
  = do fres <- termBuilder (Ctxt lvls names types) func
       pres <- termBuilder (Ctxt lvls names types) param

       (F     tyA  tyB f) <- isFunc     (getFC func)  fres
       (TTerm tyA'     a) <- isTermTerm (getFC param) pres

       case Types.decEq tyA tyA' of

         (Yes (Same Refl Refl)) =>
           Right (Res _ _ (App fc f a))

         (No msgWhyNot prfWhyNot) =>
           Left (Err fc (TypeMismatch tyA tyA'))


-- ## Func Def
termBuilder (Ctxt lvls names types) (FuncDef fc name type def body)
  = do tres <- termBuilder (Ctxt lvls names types) type
       dres <- termBuilder (Ctxt lvls names types) def

       case isNatTy (getFC type) tres of
         Right termTy =>
           do termDef <- isNat (getFC def) dres
              bres <- termBuilder (Ctxt ((IDX TERM) :: lvls)
                                  (MkName (Just name) (IDX TERM) :: names)
                                  (NatTy :: types)) body

              (TTerm tyB termB) <- isTermTerm (getFC body) bres
              case Function.validTerm (IDX TERM) (FuncParamTy (IDX TERM) NatTy tyB) of
                Yes prfWhy =>
                  Right (Res _ _ (FuncParam fc termTy termDef termB prfWhy (IsNat ChkNat)))

                No msgWhyNot prfWhyNot =>
                  Left (Err fc (InvalidFunc msgWhyNot NatTy tyB))
         Left _ =>
           do termTy <- isDataTy (getFC type) InFunc tres

              termDef <- isData (getFC def) InFunc dres

              bres <- termBuilder (Ctxt (DATA TERM :: lvls)
                                        (MkName (Just name) (DATA TERM) :: names)
                                        (DATATERM :: types)) body
              (TTerm tyB termB) <- isTermTerm (getFC body) bres
              case Function.validTerm (IDX TERM) (FuncParamTy (DATA TERM) DATATERM tyB) of
                Yes prfWhy =>
                  Right (Res _ _ (FuncParam fc termTy termDef termB prfWhy (IsData ChkData)))
                No msgWhyNot prfWhyNot =>
                  Left (Err fc (InvalidFunc msgWhyNot DATATERM tyB))
-- ## AppOver

termBuilder (Ctxt lvls names types) (AppOver fc func param)
  = do fres <- termBuilder (Ctxt lvls names types) func
       pres <- termBuilder (Ctxt lvls names types) param

       FDef u a b termF <- isFuncDef (getFC func) fres

       case isTermTerm (getFC param) pres of
         Left _ => do termP <- isData (getFC param) InFunc pres
                      case Equality.decEq a DATATERM of
                        No msg contra =>
                          Left (Err fc (TypeMismatch a DATATERM))
                        Yes prf =>
                          case prf of
                            Same idx val =>
                              case val of
                                Refl =>
                                  pure (Res _ _ (AppOver fc termF termP))
         Right (TTerm a' termP) =>
           case Equality.decEq a a' of
             No msg contra =>
               Left (Err fc (TypeMismatch a a'))

             Yes prf =>
               case prf of
                 Same idx val =>
                   case val of
                     Refl =>
                       pure (Res _ _ (AppOver fc termF termP))


-- ## AppDef
termBuilder (Ctxt lvls names types) (AppDef fc func)
  = do fres <- termBuilder (Ctxt lvls names types) func
       (FDef u a b f) <- isFuncDef (getFC func) fres
       pure (Res _ _ (AppDef fc f))

-- ## Modules \& Units \& Nats

termBuilder (Ctxt lvls names types) (EndModule fc)
  = pure (Res _ _ (EndModule fc))

termBuilder (Ctxt lvls names types) (UnitVal fc)
  = pure (Res _ _ (MkUnit fc))

-- ## Channels

-- ### Creation

termBuilder  (Ctxt lvls names types) (MkChan fc type)
  = do tres <- termBuilder (Ctxt lvls names types) type
       t <- isData (getFC type) InChan tres
       pure (Res _ _ (MkChan fc t))


-- ### Projection

-- #### Write To
termBuilder  (Ctxt lvls names types) (WriteTo fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan (getFC chan) cres
       pure (Res _ _ (WriteTo fc c))

-- #### Read To
termBuilder  (Ctxt lvls names types) (ReadFrom fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan (getFC chan) cres
       pure (Res _ _ (ReadFrom fc c))

-- ### Driving

-- #### Drive

termBuilder (Ctxt lvls names types) (Drive fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       p <- isPortWithDir (getFC port) pres OUT
       pure (Res _ _ (Drive fc p))

-- #### Catch
termBuilder (Ctxt lvls names types) (Catch fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       p <- isPortWithDir (getFC port) pres IN
       pure (Res _ _ (Catch fc p))

-- ## Operations on Ports

-- ### Casting
termBuilder (Ctxt lvls names types) (Cast fc port type toDir)
  = do pres <- termBuilder (Ctxt lvls names types) port
       tres <- termBuilder (Ctxt lvls names types) type

       (P fromDir from) <- isPort (getFC port) pres

       t <- isData (getFC type) InCast tres

       let fromP = PortTy fromDir
       let toP   = PortTy toDir

       case validCast (PortTy fromDir) (PortTy toDir) of
         (Yes prfWhy) =>
           Right (Res _ _ (Cast fc from t toDir prfWhy))
         (No msgWhyNot prfWhyNot) =>
           Left (Err fc (InvalidCast msgWhyNot fromP toP))


-- ### Slicing
termBuilder (Ctxt lvls names types) (Slice fc port start end)
  = do pres <- termBuilder (Ctxt lvls names types) port
       sres <- termBuilder (Ctxt lvls names types) start
       eres <- termBuilder (Ctxt lvls names types) end
       (P d p) <- isPort (getFC port)  pres
       s <- isNat  (getFC start) sres
       e <- isNat  (getFC end)   eres
       pure (Res _ _ (Slice fc p s e))

-- ### Conditionals

termBuilder (Ctxt lvls names types) (IfThenElse fc test true false)
  = do cres <- termBuilder (Ctxt lvls names types) test
       tres <- termBuilder (Ctxt lvls names types) true
       fres <- termBuilder (Ctxt lvls names types) false

       case isPortWithDir (getFC test) cres IN of
         Left err =>
           do c <- isBool (getFC test)  cres
              t <- isUnit (getFC true)  tres
              f <- isUnit (getFC false) fres
              pure (Res _ _ (IfThenElseC fc c t f))

         Right cc =>
           do t  <- isUnit (getFC true)  tres
              f  <- isUnit (getFC false) fres
              pure (Res _ _ (IfThenElseR fc cc t f))


-- ### Connecting Ports
termBuilder (Ctxt lvls names types) (Connect fc portL portR)
  = do lres <- termBuilder (Ctxt lvls names types) portL
       rres <- termBuilder (Ctxt lvls names types) portR

       (P da pa) <- isPort (getFC portL) lres
       (P db pb) <- isPort (getFC portR) rres

       let ptA = PortTy da
       let ptB = PortTy db

       case validFlow da db of
         (Yes x) => Right (Res _ _ (Connect fc pa pb x))

         (No msgWhyNot prfWhyNot) =>
           Left (Err fc (InvalidFlow msgWhyNot))

-- ## Gates
-- ### Not
termBuilder (Ctxt lvls names types) (NotGate fc portOut portIn)
  = do ores <- termBuilder (Ctxt lvls names types) portOut
       ires <- termBuilder (Ctxt lvls names types) portIn

       (output) <- isPortWithDir (getFC portOut) ores OUT
       (input)  <- isPortWithDir (getFC portIn)  ires IN

       let po = PortTy OUT
       let pi = PortTy IN

       pure (Res _ _ (Not fc output input))


-- ### Bin Gate

termBuilder (Ctxt lvls names types) (Gate fc kind portOut portInA portInB)
  = do po  <- termBuilder (Ctxt lvls names types) portOut
       pia <- termBuilder (Ctxt lvls names types) portInA
       pib <- termBuilder (Ctxt lvls names types) portInB

       output <- isPortWithDir (getFC portOut) po  OUT
       inputA <- isPortWithDir (getFC portInA) pia IN
       inputB <- isPortWithDir (getFC portInB) pib IN

       let po = PortTy OUT
       let pa = PortTy IN
       let pb = PortTy IN

       pure (Res _ _ (Gate fc kind output inputA inputB))


-- ### Let binding
termBuilder (Ctxt lvls names types) (Let fc name value body)
  = do (Res u tyV v) <- termBuilder (Ctxt lvls names types) value

       case validBind u tyV of
         No err contra => Left (Err (getFC value) (InvalidBind err))
         Yes prf =>
           do bres <- termBuilder (Ctxt (u::lvls)
                                        ((MkName (Just name) u)::names)
                                        (tyV::types))
                                        body

              TTerm ty b <- isTermTerm (getFC body) bres

              pure (Res _ _ (Let fc v b prf))


-- ### Sequencing
termBuilder (Ctxt lvls names types) (Seq fc left right)
  = do lres <- termBuilder (Ctxt lvls names types) left
       l    <- isUnit (getFC left) lres

       rres <- termBuilder (Ctxt lvls names types) right

       (TTerm ty r) <- isTermTerm (getFC right) rres

       case validSeq (IDX TERM) ty of
         No err contra => Left (Err (getFC right) (InvalidSeq err))
         Yes prf => pure (Res _ _ (Seq fc l r prf))

-- ## Indicies

termBuilder (Ctxt lvls names types) (Index fc i port)
  = do ires <- termBuilder (Ctxt lvls names types) i
       pres <- termBuilder (Ctxt lvls names types) port

       i' <- isNat (getFC i) ires

       (P d p)  <- isPort (getFC port) pres
       pure (Res _ _ (Index fc i' p))

termBuilder (Ctxt lvls names types) (For fc n i body)
  = do ires <- termBuilder (Ctxt lvls names types) i

       i <- isNat (getFC i) ires

       bres <- termBuilder (Ctxt (IDX TERM::lvls)
                                 ((MkName (Just n) (IDX TERM))::names)
                                 (NatTy::types))
                           body

       b <- isUnit (getFC body) bres

       pure (Res _ _ (For fc i b))


termBuilder (Ctxt lvls names types) (TyNat fc) = pure (Res _ _ (TyNat fc))
termBuilder (Ctxt lvls names types) (TyDATA fc) = pure (Res _ _ (DATATYPE fc))
termBuilder (Ctxt lvls names types) (MkNat fc n) = pure (Res _ _ (MkNat fc n))
termBuilder (Ctxt lvls names types) (MkBool fc b) = pure (Res _ _ (MkBool fc b))

termBuilder (Ctxt lvls names types) (BoolNot fc expr)
  = do eres <- termBuilder (Ctxt lvls names types) expr
       e <- isBool (getFC expr) eres
       pure (Res _ _ (BoolNot fc e))

termBuilder (Ctxt lvls names types) (NatOpCmp fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isNat (getFC l) lres
       rop <- isNat (getFC r) rres
       pure (Res _ _ (NatOpCmp fc k lop rop))

termBuilder (Ctxt lvls names types) (BoolOpBin fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isBool (getFC l) lres
       rop <- isBool (getFC r) rres
       pure (Res _ _ (BoolOpBin fc k lop rop))

termBuilder (Ctxt lvls names types) (NatOpArith fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isNat (getFC l) lres
       rop <- isNat (getFC r) rres
       pure (Res _ _ (NatOpArith fc k lop rop))

termBuilder (Ctxt lvls names types) (Size fc s)
  = do pres <- termBuilder (Ctxt lvls names types) s
       (P d p) <- isPort (getFC s) pres
       pure (Res _ _ (Size fc p))

-- [ End of Build ]


namespace Params
  export
  build : (ast : AST)
               -> Either Params.Error (SystemV Nil ModuleTy)
  build ast with (termBuilder (Ctxt Nil Nil Nil) ast)
    build ast | (Left err)
      = Left err
    build ast | (Right (Res _ ModuleTy term))
      = Right term
    build ast | (Right (Res _ type term))

      = Left (TypeMismatch ModuleTy type)

-- --------------------------------------------------------------------- [ EOF ]
