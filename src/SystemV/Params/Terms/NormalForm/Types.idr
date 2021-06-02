module SystemV.Params.Terms.NormalForm.Types

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import SystemV.Common.Utilities
import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Terms.NormalForm.Error

%default total

mutual
  namespace Nat
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      IsSize : Port.Argument.NF term -> Nat.NF (Size fc term)
      IsNat  : Nat.NF (MkNat fc n)
      IsRef  : Nat.NF (Var fc ref)
      IsOp   : Nat.NF left
            -> Nat.NF right
            -> Nat.NF (NatOpArith fc op left right)

  namespace Port
    namespace Argument
      public export
      data NF : (term : SystemV ctxt type) -> Type where
        Var      : Argument.NF (Var fc ref)
        WriteTo  : Argument.NF term -> Argument.NF (WriteTo  fc term)
        ReadFrom : Argument.NF term -> Argument.NF (ReadFrom fc term)
        Cast : Argument.NF term
            -> DataType.NF type
            -> Argument.NF (Cast fc term type dir prf)

        Slice : Argument.NF term
             -> Nat.NF a
             -> Nat.NF o
             -> Argument.NF (Slice fc term a o)

        Index : Nat.NF i
             -> {term : SystemV ctxt (PortTy dir)}
             -> Argument.NF term
             -> Argument.NF (Index fc i term)

  namespace DataType
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      TyRef : DataType.NF (Var fc ref)

      TyLogic : DataType.NF (TyLogic fc)

      TyVect : Nat.NF s
            -> DataType.NF type
            -> DataType.NF (TyVect fc s type)

namespace TermType
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    TyModule : TermType.NF (TyModule fc)
    TyUnit   : TermType.NF (TyUnit fc)
    TyNat    : TermType.NF (TyNat fc)
    TyBool   : TermType.NF (TyBool fc)
    TyChan   : DataType.NF type -> TermType.NF (TyChan fc type)
    TyPort   : DataType.NF type -> TermType.NF (TyPort fc type dir)

namespace DefaultType
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    IsNat : DefaultType.NF (TyNat fc)
    IsDTy : DefaultType.NF (DATATYPE fc)

namespace Chan
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    MkChan : DataType.NF type -> Chan.NF (MkChan fc type)

namespace Gate
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    Not : {output : SystemV ctxt (PortTy OUT)}
       -> Argument.NF output
       -> {input : SystemV ctxt (PortTy IN)}
       -> Argument.NF input
       -> Gate.NF (Not fc output input)

    Gate : {output : SystemV ctxt (PortTy OUT)}
        -> Argument.NF output
        -> {inputA,inputB : SystemV ctxt (PortTy IN)}
        -> Argument.NF inputA
        -> Argument.NF inputB
        -> Gate.NF (Gate fc k output inputA inputB)

namespace Bool
  public export
  data NF : (term : SystemV ctxt type) -> Type where
    IsBool : Bool.NF (MkBool fc b)
    IsRef  : Bool.NF (Var fc  ref)
    IsBoolNot : Bool.NF expr
             -> Bool.NF (BoolNot fc expr)

    IsBoolOp : {op : BoolBinOp}
            -> {left, right : SystemV ctxt BoolTy}
            -> Bool.NF left
            -> Bool.NF right
            -> Bool.NF (BoolOpBin fc op left right)

    IsBoolOpNat : Nat.NF left
               -> Nat.NF right
               -> Bool.NF (NatOpCmp fc op left right)

mutual
  namespace Function
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      Func : TermType.NF ty
          -> {rest : SystemV (ctxt += a) typeR}
          -> Function.Body.NF rest
          -> Types.Function.NF (Func fc ty rest prf vld)

    namespace Default
      public export
      data NF : (term : SystemV ctxt type) -> Type where
        FuncParam : DefaultType.NF ty
                 -> {def : SystemV ctxt a}
                 -> Function.Default.Argument.NF def
                 -> {rest : SystemV (ctxt += a) typeR}
                 -> Function.Body.NF rest
                 -> Function.Default.NF (FuncParam fc ty def rest prf vld)

        FuncParamNested : DefaultType.NF ty
                       -> {def : SystemV ctxt a}
                       -> Function.Default.Argument.NF def
                       -> {rest : SystemV (ctxt += a) typeR}
                       -> Function.Default.NF rest
                       -> Function.Default.NF (FuncParam fc ty def rest prf vld)

        FuncParamFunc : DefaultType.NF ty
                     -> {def : SystemV ctxt a}
                     -> Function.Default.Argument.NF def
                     -> {rest : SystemV (ctxt += a) typeR}
                     -> Types.Function.NF rest
                     -> Function.Default.NF (FuncParam fc ty def rest prf vld)

      namespace Argument
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          IsNat  : Nat.NF term
                -> Function.Default.Argument.NF term

          IsType : DataType.NF term
                -> Function.Default.Argument.NF term

    namespace Argument
      public export
      data NF : (term : SystemV ctxt type) -> Type where
        MkUnit   : Function.Argument.NF (MkUnit fc)
        Var      : Port.Argument.NF term
                -> Function.Argument.NF term

    namespace Body

      public export
      data NF : (term : SystemV ctxt type) -> Type where
        IsEmpty : Function.Body.NF (EndModule fc)
        IsSeq  : Sequence.NF term -> Function.Body.NF term
        IsFunc : Types.Function.NF term -> Function.Body.NF term
        IsLet  : Function.Body.Let.NF term -> Function.Body.NF term

      namespace Let
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          DeclD : DataType.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let fc value rest prf)

          DeclMP : Function.Default.NF value
                -> {rest  : SystemV (ctxt += a) b}
                -> Function.Body.NF rest
                -> Function.Body.Let.NF (Let fc value rest prf)

          DeclM : Types.Function.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let fc value rest prf)

          InstW : Chan.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let fc value rest prf)

          InstM : Application.NF value
               -> {rest  : SystemV (ctxt += a) b}
               -> Function.Body.NF rest
               -> Function.Body.Let.NF (Let fc value rest prf)

      namespace Sequence
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          EndModule : Sequence.NF (EndModule fc)
          UnitVal   : Sequence.NF (MkUnit fc)
          Drive   : Port.Argument.NF term -> Sequence.NF (Drive fc term)
          Catch   : Port.Argument.NF term -> Sequence.NF (Catch fc term)
          Connect : {left  : SystemV ctxt (PortTy dirL)}
                 -> Port.Argument.NF left
                 -> {right : SystemV ctxt (PortTy dirR)}
                 -> Port.Argument.NF right
                 -> {prf   : ValidFlow dirL dirR}
                 -> Sequence.NF (Connect fc left right prf)

          Cond : Conditional.NF term
              -> Sequence.NF term

          For : For.NF term
             -> Sequence.NF term

          Gate : Gate.NF term -> Sequence.NF term

          IsLet : Function.Body.Let.NF term -> Sequence.NF term

          Seq : {left : SystemV ctxt UnitTy}
             -> Sequence.NF left
             -> {type : TYPE (IDX TERM)}
             -> {right : SystemV ctxt type}
             -> Sequence.NF right
             -> {prf : ValidSeq (IDX TERM) type}
             -> Sequence.NF (Seq fc left right prf)

      namespace Conditional
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          IfThenElseR : Port.Argument.NF test
                     -> Function.Body.NF true
                     -> Function.Body.NF false
                     -> Conditional.NF (IfThenElseR fc test true false)
          IfThenElseC : Bool.NF test
                     -> Function.Body.NF true
                     -> Function.Body.NF false
                     -> Conditional.NF (IfThenElseC fc test true false)

      namespace For
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          ForEach : Nat.NF i
                 -> {body : SystemV (ctxt += NatTy) UnitTy}
                 -> Function.Body.NF body
                 -> For.NF (For fc i body)

  namespace Application

      namespace Function
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          AppRef  : Function.Argument.NF param
                 -> Application.Function.NF (App fc (Var fcv ref) param)

          AppRec  : {func : SystemV ctxt (FuncTy a b)}
                 -> Application.NF func
                 -> {param : SystemV ctxt a}
                 -> Function.Argument.NF param
                 -> Application.Function.NF (App fc func param)

      namespace Over
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          AppOverRef : Function.Default.Argument.NF param
                   -> Application.Over.NF (AppOver fc (Var fcv ref) param)

          AppOverFunc : {func : SystemV ctxt (FuncParamTy u a b)}
                     -> Application.Function.NF func
                     -> {param : SystemV ctxt a}
                     -> Function.Default.Argument.NF param
                     -> Application.Over.NF (AppOver fc func param)

          AppOverDef  : {func : SystemV ctxt (FuncParamTy u a b)}
                     -> Application.Default.NF func
                     -> {param : SystemV ctxt a}
                     -> Function.Default.Argument.NF param
                     -> Application.Over.NF (AppOver fc func param)

          AppOverRec  : {func : SystemV ctxt (FuncParamTy u a b)}
                     -> Application.Over.NF func
                     -> {param : SystemV ctxt a}
                     -> Function.Default.Argument.NF param
                     -> Application.Over.NF (AppOver fc func param)

      namespace Default
        public export
        data NF : (term : SystemV ctxt type) -> Type where
          AppDefRef : Application.Default.NF (AppDef fc (Var fcv ref))

          AppDefFunc  : {func : SystemV ctxt (FuncParamTy u a b)}
                     -> Application.Function.NF func
                     -> Application.Default.NF (AppDef fc func)

          AppDefOver  : {func : SystemV ctxt (FuncParamTy u a b)}
                     -> Application.Over.NF func
                     -> Application.Default.NF (AppDef fc func)

          AppDefRec  : {func : SystemV ctxt (FuncParamTy u a b)}
                    -> Application.Default.NF func
                    -> Application.Default.NF (AppDef fc func)

      public export
      data NF : (term : SystemV ctxt type) -> Type where
         AppFunc : Application.Function.NF term -> Application.NF term
         AppDef  : Application.Default.NF term -> Application.NF term
         AppOver : Application.Over.NF term -> Application.NF term


namespace Design
  mutual
    public export
    data NF : (term : SystemV ctxt type) -> Type where
      IsTop : Application.Function.NF (App fc term (MkUnit fcu))
           -> Design.NF (App fc term (MkUnit fcu))
      IsDecl : Design.Decl.NF term -> Design.NF term

    namespace Decl
      public export
      data NF : (term : SystemV ctxt type) -> Type where

        DeclD : DataType.NF value
             -> {rest  : SystemV (ctxt += a) b}
             -> Design.NF rest
             -> Design.Decl.NF (Let fc value rest prf)

        DeclMP : Function.Default.NF value
              -> {rest  : SystemV (ctxt += a) b}
              -> Design.NF rest
              -> Design.Decl.NF (Let fc value rest prf)

        DeclM : Types.Function.NF value
             -> {rest  : SystemV (ctxt += a) b}
             -> Design.NF rest
             -> Design.Decl.NF (Let fc value rest prf)

-- [ EOF ]
