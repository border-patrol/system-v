module SystemV.Core.Terms.NormalForm

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import SystemV.Common.Utilities
import SystemV.Core.Types
import SystemV.Core.Terms

%default total

data NF : SystemV ctxt type -> Type where
  DataType : {type : TYPE (DATA TYPE)}
          -> {datatype : SystemV ctxt type}
          -> NF datatype



  TyUnit : NF TyUnit
  TyModule : NF TyModule
  TyChan   : NF (TyChan type)
  TyPort   : NF (TyPort type dir)

  ||| End of a function
  SeqEndM : {left : SystemV ctxt UnitTy}
         -> NF left
         -> {right : SystemV ctxt type}
   --      -> (prf : IsEndModule right)
   --      -> IsEndModule right prf
         -> NF (Seq left right)

  ||| End of a if block, and left nested sequences.
  SeqEndU : {left : SystemV ctxt UnitTy}
         -> {right : SystemV ctxt UnitTy}
         -> NF left
         -> NF right
         -> NF (Seq left right)

  Var : NF (Var ref)

  MDecl : {body : SystemV (p::ctxt) typeB}
       -> NF body
       -> {rest : SystemV (FuncTy p typeB::ctxt) typeR}
       -> NF rest
       -> NF (Let (Func type body prf vld) rest)

  MInst : {func : SystemV ctxt (FuncTy a b)}
       -> NF func
       -> {value : SystemV ctxt a}
       -> NF value
       -> {rest : SystemV (ctxt += b) typeR}
       -> NF rest
       -> NF (Let (App func value) rest)

  Typedef : {type : TYPE (DATA TERM)}
         -> {datatype : SystemV ctxt type}
         -> {rest : SystemV (ctxt += type) typeR}
         -> NF rest
         -> NF (Let datatype rest)

  Wire : {type : TYPE (DATA TYPE)}
      -> {datatype : SystemV ctxt type}
      -> {rest : SystemV (ctxt += ChanTy type) typeR }
      -> NF rest
      -> NF (Let (MkChan datatype) rest)

  MkUnit : NF MkUnit

  WriteTo : NF chan
         -> NF (WriteTo chan)

  ReadFrom : NF chan
          -> NF (ReadFrom chan)

  Drive : NF chan
       -> NF (Drive chan)

  Catch : NF chan
       -> NF (Catch chan)

  IfThenElseR : NF test
             -> NF true
             -> NF false
             -> NF (IfThenElseR test true false)

  Connect : {left : SystemV ctxt (PortTy ty l)}
         -> NF left
         -> {right : SystemV ctxt (PortTy ty r)}
         -> NF right
         -> {prf : ValidFlow l r}
         -> NF (Connect left right prf)

  Cast : NF port
      -> NF (Cast port prf)

  Slice : NF port
       -> NF (Slice port a o prf)

  Index : NF port
       -> NF (Index i port prf)

  Not : {out : SystemV ctxt (PortTy ty OUT)}
     -> NF out
     -> {inp : SystemV ctxt (PortTy ty IN)}
     -> NF inp
     -> NF (Not out inp)

  Gate : {out : SystemV ctxt (PortTy ty OUT)}
      -> NF out
      -> {ina, inb : SystemV ctxt (PortTy ty IN)}
      -> NF ina
      -> NF inb
      -> NF (Gate k out ina inb)

data Error : Type where
--  ViewErr : Views.Error -> NormalForm.Error
  NotUnit : Equality.Error -> NormalForm.Error
  Err     : NormalForm.Error -> NormalForm.Error
  NotAllowed : Error
  LeftSeq : NormalForm.Error -> NormalForm.Error
  NotNormalForm : Error

nf : (term : SystemV ctxt type)
  -> DecInfo NormalForm.Error (NF term)

nf TyUnit = Yes TyUnit

nf TyModule = Yes TyModule

nf (TyChan typeD) = Yes TyChan

nf (TyPort desc dir) = Yes TyPort

nf TyLogic = Yes DataType

nf (TyVect s typeE) = Yes DataType

nf (Var idx) = Yes Var

nf (Func x body prf vld) = ?nf_rhs_9

nf (App func value) = ?nf_rhs_10

nf MkUnit = Yes MkUnit

nf EndModule = ?nf_rhs_12

nf (MkPort typeD dir) = ?nf_rhs_13

nf (MkChan typeD) = ?nf_rhs_14

nf (WriteTo chan)
  = decInfoDo $ do prf <- nf chan `otherwise` ?writeToChanNotNF
                   pure (WriteTo prf)

nf (ReadFrom chan)
  = decInfoDo $ do prf <- nf chan `otherwise` ?readFromToChanNotNF
                   pure (ReadFrom prf)


nf (Drive chan)
  = decInfoDo $ do prf <- nf chan `otherwise` ?driveChanNotNF
                   pure (Drive prf)

nf (Catch chan)
  = decInfoDo $ do prf <- nf chan `otherwise` ?catchChanNotNF
                   pure (Catch prf)

nf (IfThenElseR test tt ff)
  = decInfoDo $ do cprf <- nf test `otherwise` ?ifTestNotNF
                   tprf <- nf tt   `otherwise` ?ifTrueNotNF
                   fprf <- nf ff   `otherwise` ?ifFalseNotNF
                   pure (IfThenElseR cprf tprf fprf)

nf (Connect portL portR prf) = ?nf_rhs_20
nf (Cast portA prf) = ?nf_rhs_21
nf (Slice port alpha omega prf) = ?nf_rhs_22
nf (Index idx port prf) = ?nf_rhs_23

nf (Not portO portI)
  = decInfoDo $ do o <- nf portO `otherwise` ?notOutNotNF
                   i <- nf portI `otherwise` ?notInNotNF
                   pure (Not o i)


nf (Gate kind portO portIA portIB)
  = decInfoDo $ do o <- nf portO  `otherwise` ?gateOutNotNF
                   a <- nf portIA `otherwise` ?gateInANotNF
                   b <- nf portIB `otherwise` ?gateInBNotNF
                   pure (Gate o a b)

nf (Let value body) = ?nf_rhs_26

--nf (Seq left EndModule)
--  = decInfoDo $ do l <- nf left `otherwise` ?seqEndMLeftNotNF
--               pure (SeqEndM l)

nf (Seq left right {type}) = ?rhs

-- [ EOF ]
