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
termBuilder (Ctxt lvls names types) (TyUnit _)
  = pure (Res _ _ TyUnit)

-- ### Logic
termBuilder (Ctxt lvls names types) (TyLogic _)
  = pure (Res _ _ TyLogic)

-- ### Vectors
termBuilder (Ctxt lvls names types) (TyVect fc size type)
  = do sres <- termBuilder (Ctxt lvls names types) size
       tres <- termBuilder (Ctxt lvls names types) type
       s <- isNat (getFC size) sres
       t <- isData (getFC type) InVector tres
       pure (Res _ _ (TyVect s t))

-- ### Ports
termBuilder (Ctxt lvls names types) (TyPort fc type dir)
  = do tres <- termBuilder (Ctxt lvls names types) type
       t    <- isData (getFC type) InVector tres
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
                  Right (Res _ _ (Func termP termB chk prfWhy))
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
           Right (Res _ _ (App f a))

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
                  Right (Res _ _ (FuncParam termTy termDef termB prfWhy (IsNat ChkNat)))

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
                  Right (Res _ _ (FuncParam termTy termDef termB prfWhy (IsData ChkData)))
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
                                  pure (Res _ _ (AppOver termF termP))
         Right (TTerm a' termP) =>
           case Equality.decEq a a' of
             No msg contra =>
               Left (Err fc (TypeMismatch a a'))

             Yes prf =>
               case prf of
                 Same idx val =>
                   case val of
                     Refl =>
                       pure (Res _ _ (AppOver termF termP))


-- ## AppDef
termBuilder (Ctxt lvls names types) (AppDef fc func)
  = do fres <- termBuilder (Ctxt lvls names types) func
       (FDef u a b f) <- isFuncDef (getFC func) fres
       pure (Res _ _ (AppDef f))

-- ## Modules \& Units \& Nats

termBuilder (Ctxt lvls names types) (EndModule fc)
  = pure (Res _ _ EndModule)

termBuilder (Ctxt lvls names types) (UnitVal fc)
  = pure (Res _ _ MkUnit)

-- ## Channels

-- ### Creation

termBuilder  (Ctxt lvls names types) (MkChan fc type)
  = do tres <- termBuilder (Ctxt lvls names types) type
       t <- isData (getFC type) InChan tres
       pure (Res _ _ (MkChan t))


-- ### Projection

-- #### Write To
termBuilder  (Ctxt lvls names types) (WriteTo fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan (getFC chan) cres
       pure (Res _ _ (WriteTo c))

-- #### Read To
termBuilder  (Ctxt lvls names types) (ReadFrom fc chan)
  = do cres <- termBuilder (Ctxt lvls names types) chan
       c <- isChan (getFC chan) cres
       pure (Res _ _ (ReadFrom c))

-- ### Driving

-- #### Drive

termBuilder (Ctxt lvls names types) (Drive fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       p <- isPortWithDir (getFC port) pres OUT
       pure (Res _ _ (Drive p))

-- #### Catch
termBuilder (Ctxt lvls names types) (Catch fc port)
  = do pres <- termBuilder (Ctxt lvls names types) port
       p <- isPortWithDir (getFC port) pres IN
       pure (Res _ _ (Catch p))

-- ## Operations on Ports

-- ### Casting
termBuilder (Ctxt lvls names types) (Cast fc port type toDir)
  = do pres <- termBuilder (Ctxt lvls names types) port
       tres <- termBuilder (Ctxt lvls names types) type

       (P fromDir from) <- isPort (getFC port) pres

       let fromP = PortTy fromDir
       let toP   = PortTy toDir

       case validCast (PortTy fromDir) (PortTy toDir) of
         (Yes prfWhy) =>
           Right (Res _ _ (Cast from toDir prfWhy))
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
       pure (Res _ _ (Slice p s e))

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
              pure (Res _ _ (IfThenElseC c t f))

         Right cc =>
           do t  <- isUnit (getFC true)  tres
              f  <- isUnit (getFC false) fres
              pure (Res _ _ (IfThenElseR cc t f))


-- ### Connecting Ports
termBuilder (Ctxt lvls names types) (Connect fc portL portR)
  = do lres <- termBuilder (Ctxt lvls names types) portL
       rres <- termBuilder (Ctxt lvls names types) portR

       (P da pa) <- isPort (getFC portL) lres
       (P db pb) <- isPort (getFC portR) rres

       let ptA = PortTy da
       let ptB = PortTy db

       case validFlow da db of
         (Yes x) => Right (Res _ _ (Connect pa pb x))

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

       pure (Res _ _ (Not output input))


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

       pure (Res _ _ (Gate kind output inputA inputB))


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
  = do ires <- termBuilder (Ctxt lvls names types) i
       pres <- termBuilder (Ctxt lvls names types) port

       i' <- isNat (getFC i) ires

       (P d p)  <- isPort (getFC port) pres
       pure (Res _ _ (Index i' p))

termBuilder (Ctxt lvls names types) (For fc n i port)
  = do ires <- termBuilder (Ctxt lvls names types) i
       bres <- termBuilder (Ctxt lvls names types) port

       i <- isNat (getFC i) ires

       (FDef u a b term) <- isFuncDef (getFC port) bres

       case Equality.decEq (FuncParamTy (IDX TERM) NatTy UnitTy)
                           (FuncParamTy u          a     b) of
         (Yes prf) =>
           case prf of
             (Same Refl prfVal) =>
               case prfVal of
                 Refl => Right (Res _ _ (For i term))
         (No msgWhyNot prfWhyNot) =>
           Left (TypeMismatch
                           (FuncParamTy (IDX TERM) NatTy UnitTy)
                           (FuncParamTy u          a     b))

termBuilder (Ctxt lvls names types) (TyNat fc) = pure (Res _ _ TyNat)
termBuilder (Ctxt lvls names types) (TyDATA fc) = pure (Res _ _ DATATYPE)
termBuilder (Ctxt lvls names types) (MkNat fc n) = pure (Res _ _ (MkNat n))
termBuilder (Ctxt lvls names types) (MkBool fc b) = pure (Res _ _ (MkBool b))

termBuilder (Ctxt lvls names types) (BoolNot fc expr)
  = do eres <- termBuilder (Ctxt lvls names types) expr
       e <- isBool (getFC expr) eres
       pure (Res _ _ (BoolNot e))

termBuilder (Ctxt lvls names types) (NatOpCmp fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isNat (getFC l) lres
       rop <- isNat (getFC r) rres
       pure (Res _ _ (NatOpCmp k lop rop))

termBuilder (Ctxt lvls names types) (BoolOpBin fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isBool (getFC l) lres
       rop <- isBool (getFC r) rres
       pure (Res _ _ (BoolOpBin k lop rop))

termBuilder (Ctxt lvls names types) (NatOpArith fc k l r)
  = do lres <- termBuilder (Ctxt lvls names types) l
       rres <- termBuilder (Ctxt lvls names types) r
       lop <- isNat (getFC l) lres
       rop <- isNat (getFC r) rres
       pure (Res _ _ (NatOpArith k lop rop))

termBuilder (Ctxt lvls names types) (Size fc s)
  = do pres <- termBuilder (Ctxt lvls names types) s
       (P d p) <- isPort (getFC s) pres
       pure (Res _ _ (Size p))

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
