module SystemV.Core.Terms.NormalForm.Types

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import SystemV.Common.Utilities
import SystemV.Core.Types
import SystemV.Core.Terms

import SystemV.Core.Terms.NormalForm.Error

%default total

namespace DataType
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    TyRef : DataType.NF (Var ref)

    TyLogic : DataType.NF TyLogic

    TyVect : DataType.NF type
          -> DataType.NF (TyVect s type)

namespace TermType
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    TyModule : TermType.NF TyModule
    TyUnit : TermType.NF TyUnit
    TyChan : DataType.NF type -> TermType.NF (TyChan type)
    TyPort : DataType.NF type -> TermType.NF (TyPort type dir)

namespace Port
  namespace Argument
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      Var      : Argument.NF (Var ref)
      WriteTo  : Argument.NF term -> Argument.NF (WriteTo  term)
      ReadFrom : Argument.NF term -> Argument.NF (ReadFrom term)
      Slice    : Argument.NF term -> Argument.NF (Slice term a o prf)
      Index    : Argument.NF term -> Argument.NF (Index i term prf)
      Cast     : Argument.NF term -> Argument.NF (Cast  term prf)

namespace Chan
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    MkChan : DataType.NF type -> Chan.NF (MkChan type)

namespace Gate
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    Not : {output : SystemV ctxt (PortTy ty OUT)}
       -> Argument.NF output
       -> {input : SystemV ctxt (PortTy ty IN)}
       -> Argument.NF input
       -> Gate.NF (Not output input)

    Gate : {output : SystemV ctxt (PortTy ty OUT)}
        -> Argument.NF output
        -> {inputA,inputB : SystemV ctxt (PortTy ty IN)}
        -> Argument.NF inputA
        -> Argument.NF inputB
        -> Gate.NF (Gate k output inputA inputB)


mutual
  namespace Function
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      Func : TermType.NF ty
          -> {rest : SystemV (ctxt += a) typeR}
          -> Function.Body.NF rest
          -> Function.NF (Func ty rest prf vld)


    namespace Argument
      public export
      data NF : (term : SystemV ctxt type) -> Type where
        MkUnit   : Function.Argument.NF MkUnit
        Var      : Port.Argument.NF term
                -> Function.Argument.NF term

    namespace Body

      public export
      data NF : (term : SystemV ctxt type) -> Type where
        IsEmpty : Function.Body.NF EndModule
        IsSeq  : Sequence.NF term -> Function.Body.NF term
        IsFunc : Function.NF term -> Function.Body.NF term
        IsLet  : Function.Body.Let.NF term -> Function.Body.NF term

      namespace Let
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          DeclD : DataType.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let value rest prf)

          DeclM : Function.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let value rest prf)

          InstW : Chan.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let value rest prf)

          InstM : Application.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let value rest prf)

      namespace Sequence
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          EndModule : Sequence.NF EndModule
          Drive   : Port.Argument.NF term -> Sequence.NF (Drive term)
          Catch   : Port.Argument.NF term -> Sequence.NF (Catch term)
          Connect : {left  : SystemV ctxt (PortTy ty dirL)}
                 -> Port.Argument.NF left
                 -> {right : SystemV ctxt (PortTy ty dirR)}
                 -> Port.Argument.NF right
                 -> {prf   : ValidFlow dirL dirR}
                 -> Sequence.NF (Connect left right prf)

          Cond : Conditional.NF term
              -> Sequence.NF term

          Gate : Gate.NF term -> Sequence.NF term

          IsLet : Function.Body.Let.NF term -> Sequence.NF term

          Seq : {left : SystemV ctxt UnitTy}
             -> Sequence.NF left
             -> {type : TYPE (IDX TERM)}
             -> {right : SystemV ctxt type}
             -> Sequence.NF right
             -> {prf : ValidSeq (IDX TERM) type}
             -> Sequence.NF (Seq left right prf)

      namespace Conditional
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          IfThenElse : Port.Argument.NF test
                    -> Function.Body.NF true
                    -> Function.Body.NF false
                    -> Conditional.NF (IfThenElseR test true false)


  namespace Application
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      AppRef  : Function.Argument.NF param
             -> Application.NF (App (Var ref) param)

      AppRec  : {func : SystemV ctxt (FuncTy a b)}
             -> Application.NF func
             -> {param : SystemV ctxt a}
             -> Function.Argument.NF param
             -> Application.NF (App func param)

--      AppFunc : {func : SystemV ctxt (FuncTy a b)}
--             -> Function.NF func
--             -> {param : SystemV ctxt a}
--             -> Function.Argument.NF param
--             -> Application.NF (App func param)


namespace Design
  mutual
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      IsTop : Application.NF (App term MkUnit)
           -> Design.NF (App term MkUnit)
      IsDecl : Design.Decl.NF term -> Design.NF term

    namespace Decl
      public export
      data NF : (term : SystemV ctxt type) -> Type where

        DeclD : DataType.NF value
             -> {rest  : SystemV (ctxt += a) b}
             -> Design.NF rest
             -> Design.Decl.NF (Let value rest prf)

        DeclM : Function.NF value
             -> {rest  : SystemV (ctxt += a) b}
             -> Design.NF rest
             -> Design.Decl.NF (Let value rest prf)

-- [ EOF ]
