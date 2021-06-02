module SystemV.Params.Terms.NormalForm.Proofs

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Terms.NormalForm.Error
import SystemV.Params.Terms.NormalForm.Types

%default total

NormalForm : Type -> Type
NormalForm = Either NormalForm.Error

mutual
  namespace Nat
    export
    nf : (term : SystemV ctxt type)
              -> NormalForm (Nat.NF term)
    nf (Size _ p)
      = do p <- Port.Argument.nf p
           pure (IsSize p)

    nf (MkNat _ n) = pure IsNat

    nf (Var _ ref) = pure IsRef

    nf (NatOpArith _ op left right)
      = do l <- Nat.nf left
           r <- Nat.nf right
           pure (IsOp l r)

    nf term = Left (Err (getFC term) InvalidNat)

  namespace Port
    namespace Argument
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Port.Argument.NF term)

      nf (Var _ idx) = Right Var
      nf (WriteTo _ port)
        = do prf <- Port.Argument.nf port
             pure (WriteTo prf)

      nf (ReadFrom _ port)
        = do p <- Port.Argument.nf port
             pure (ReadFrom p)

      nf (Cast _ port type dir prf)
        = do p <- Port.Argument.nf port
             t <- DataType.nf type
             pure (Cast p t)

      nf (Slice _ port alpha omega)
        = do p <- Port.Argument.nf port
             a <- Nat.nf alpha
             o <- Nat.nf omega
             pure (Slice p a o)

      nf (Index _ idx port)
        = do i <- Nat.nf idx
             prf <- Port.Argument.nf port
             pure (Index i prf)

      nf term = Left (Err (getFC term) InvalidPortArgument)



  namespace DataType
    export
    nf : (term : SystemV ctxt type)
              -> NormalForm (DataType.NF term)

    nf (Var _ idx) = Right TyRef
    nf (TyLogic _) = Right TyLogic
    nf (TyVect _ s typeE)
      = do s' <- Nat.nf s
           prf <- DataType.nf typeE
           pure (TyVect s' prf)


    nf term = Left (Err (getFC term) IsNotDataType)

namespace TermType
  export
  nf : (term : SystemV ctxt type)
            -> NormalForm (TermType.NF term)

  nf (TyModule _) = Right TyModule
  nf (TyUnit _)   = Right TyUnit
  nf (TyChan _ ty)
    = do prf <- DataType.nf ty
         pure (TyChan prf)

  nf (TyPort _ ty dir)
    = do prf <- DataType.nf ty
         pure (TyPort prf)

  nf term = Left (Err (getFC term) IsNotTermType)

namespace DefaultType

  export
  nf : (term : SystemV ctxt type)
            -> NormalForm (DefaultType.NF term)
  nf (DATATYPE fc) = pure IsDTy
  nf (TyNat fc)    = pure IsNat
  nf term = Left (Err (getFC term) InvalidType)

namespace Chan
  export
  nf : (term : SystemV ctxt type)
            -> NormalForm (Chan.NF term)

  nf (MkChan _ ty)
    = do prf <- DataType.nf ty
         pure (MkChan prf)

  nf term = Left (Err (getFC term) InvalidMkChan)

namespace Gate
  export
  nf : (term : SystemV ctxt type)
            -> NormalForm (Gate.NF term)

  nf (Not _ portO portI)
    = do po <- Port.Argument.nf portO
         pi <- Port.Argument.nf portI
         pure (Not po pi)

  nf (Gate _ kind portO portIA portIB)
    = do po <- Port.Argument.nf portO
         pi <- Port.Argument.nf portIA
         pj <- Port.Argument.nf portIB
         pure (Gate po pi pj)

  nf term = Left (Err (getFC term) InvalidGate)

namespace Bool
  export
  nf : (term : SystemV ctxt type)
            -> NormalForm (Bool.NF term)

  nf (MkBool _ b) = pure IsBool
  nf (Var _ ref)  = pure IsRef

  nf (BoolNot _ expr)
    = do e <- Bool.nf expr
         pure (IsBoolNot e)

  nf (NatOpCmp _ op left right)
    = do l <- Nat.nf left
         r <- Nat.nf right
         pure (IsBoolOpNat l r)

  nf term = Left (Err (getFC term) InvalidBool)

mutual
  namespace Function
    export
    nf : (term : SystemV ctxt type)
              -> NormalForm (Types.Function.NF term)
    nf (Func _ ty body prf vld)
      = do prfT <- TermType.nf ty
           prfB <- Function.Body.nf body
           pure (Func prfT prfB)
    nf term = Left (Err (getFC term) InvalidFunc)

    namespace Argument
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Function.Argument.NF term)
      nf (MkUnit _) = Right MkUnit
      nf term
        = do prf <- Port.Argument.nf term
             pure (Var prf)

    namespace Default
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Function.Default.NF term)

      nf (FuncParam _ ty def rest prf vld)
        = do t <- DefaultType.nf ty
             d <- Function.Default.Argument.nf def
             case Function.Body.nf rest of
               Right p => pure (FuncParam t d p)
               Left _  =>
                 case Function.Default.nf rest of
                   Right p => pure (FuncParamNested t d p)
                   Left _  =>
                     do p <- Proofs.Function.nf rest
                        pure (FuncParamFunc t d p)

      nf term = Left (Err (getFC term) InvalidFunc)

      namespace Argument
        export
        nf : (term : SystemV ctxt type)
                  -> NormalForm (Function.Default.Argument.NF term)
        nf term
          = case Nat.nf term of
              Right p => pure (IsNat p)
              Left _ =>
                do d <- DataType.nf term
                   pure (IsType d)

    namespace Body
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Function.Body.NF term)

      nf (Func _ x body prf vld)
        = do prf <- Function.nf (Func _ x body prf vld)
             pure (IsFunc prf)

      nf (EndModule _) = Right IsEmpty

      nf (Let _ value body prf)
        = do prf <- Function.Body.Let.nf (Let _ value body prf)
             pure (IsLet prf)

      nf (Seq _ left right prf)
        = do prf <- Sequence.nf (Seq _ left right prf)
             pure (IsSeq prf)

      nf term = Left (Err (getFC term) InvalidFuncBody)

      namespace Let

        export
        nf : (term : SystemV ctxt type)
                  -> NormalForm (Function.Body.Let.NF term)
        nf (Let _ value body prf)
          = case DataType.nf value of
              Right v => do r <- Function.Body.nf body
                            pure (DeclD v r)

              Left _ =>
                case Proofs.Function.nf value of
                  Right v => do r <- Function.Body.nf body
                                pure (DeclM v r)

                  Left _ =>
                    case Function.Default.nf value of
                      Right v => do r <- Function.Body.nf body
                                    pure (DeclMP v r)

                      Left _ =>
                        case Chan.nf value of
                          Right v => do r <- Function.Body.nf body
                                        pure (InstW v r)

                          Left _ => do v <- Application.nf value
                                       r <- Function.Body.nf body
                                       pure (InstM v r)

        nf term = Left (Err (getFC term) InvalidFuncLet)

      namespace Sequence

        export
        nf : (term : SystemV ctxt type)
                  -> NormalForm (Sequence.NF term)

        nf (EndModule _) = Right EndModule
        nf (MkUnit _)    = Right UnitVal

        nf (Drive _ chan)
          = do prf <- Port.Argument.nf chan
               pure (Drive prf)

        nf (Catch _ chan)
          = do prf <- Port.Argument.nf chan
               pure (Catch prf)

        nf (Connect _ portL portR prf)
          = do prfL <- Port.Argument.nf portL
               prfR <- Port.Argument.nf portR
               pure (Connect prfL prfR)

        nf (Let _ value body prf)
          = do prf <- Function.Body.Let.nf (Let _ value body prf)
               pure (IsLet prf)

        nf (Seq _ left right prf)
          = do l <- Sequence.nf left
               r <- Sequence.nf right
               pure (Seq l r)

        nf term
          = case Conditional.nf term of
              Right c => pure (Cond c)
              Left _  =>
                case Gate.nf term of
                  Right g => pure (Gate g)
                  Left _ =>
                    do f <- For.nf term
                       pure (For f)


      namespace Conditional
        export
        nf : (term : SystemV ctxt type)
                  -> NormalForm (Conditional.NF term)

        nf (IfThenElseR _ test true false)
          = do prfP <- Port.Argument.nf test
               prfT <- Function.Body.nf true
               prfF <- Function.Body.nf false
               pure (IfThenElseR prfP prfT prfF)

        nf (IfThenElseC _ test true false)
          = do prfP <- Bool.nf test
               prfT <- Function.Body.nf true
               prfF <- Function.Body.nf false
               pure (IfThenElseC prfP prfT prfF)

        nf term = Left (Err (getFC term) InvalidConditional)

      namespace For
        export
        nf : (term : SystemV ctxt type)
                   -> NormalForm (For.NF term)
        nf (For _ i body)
          = do i' <- Nat.nf i
               r  <- Function.Body.nf body
               pure (ForEach i' r)
        nf term = Left (Err (getFC term) InvalidFor)

  namespace Application
    export
    nf : (term : SystemV ctxt type)
              -> NormalForm (Application.NF term)
    nf term
      = case Application.Function.nf term of
          Right f => pure (AppFunc f)
          Left _ =>
            case Application.Default.nf term of
              Right f => pure (AppDef f)
              Left _ =>
                do f <- Application.Over.nf term
                   pure (AppOver f)

    namespace Function
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Application.Function.NF term)

      nf (App _ (Var _ ref) param)
        = do prf <- Function.Argument.nf param
             pure (AppRef prf)
      nf (App _ func param)
        = do f <- Application.nf func
             p <- Function.Argument.nf param
             pure (AppRec f p)

      nf term = Left (Err (getFC term) InvalidApp)

    namespace Over
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Application.Over.NF term)

      nf (AppOver _ (Var _ ref) param)
        = do prf <- Function.Default.Argument.nf param
             pure (AppOverRef prf)

      nf (AppOver _ func param)
        = case Application.Function.nf func of
            Right f => do p <- Function.Default.Argument.nf param
                          pure (AppOverFunc f p)

            Left _ =>
              case Application.Default.nf func of
                Right f => do p <- Function.Default.Argument.nf param
                              pure (AppOverDef f p)
                Left _ =>
                  do f <- Application.Over.nf func
                     p <- Function.Default.Argument.nf param
                     pure (AppOverRec f p)

      nf term = Left (Err (getFC term) InvalidApp)

    namespace Default
      export
      nf : (term : SystemV ctxt type)
                -> NormalForm (Application.Default.NF term)

      nf (AppDef _ (Var _ ref)) = pure AppDefRef

      nf (AppDef _ func)
        = case Application.Function.nf func of
            Right f => pure (AppDefFunc f)

            Left _ =>
              case Application.Over.nf func of
                Right f => pure (AppDefOver f )
                Left _ =>
                  do f <- Application.Default.nf func
                     pure (AppDefRec f)

      nf term = Left (Err (getFC term) InvalidApp)


namespace Design
  mutual

    export
    nf : (term : SystemV ctxt type)
              -> Either NormalForm.Error
                        (Design.NF term)
    nf (App _ func (MkUnit _))
      = do prf <- Application.Function.nf (App _ func (MkUnit _))
           pure (IsTop prf)

    nf (Let _ value body prf)
      = do prf <- Design.Decl.nf (Let _ value body prf)
           pure (IsDecl prf)

    nf term = Left (Err (getFC term) InvalidDesignBody)

    namespace Decl
      export
      nf : (term : SystemV ctxt type)
                -> Either NormalForm.Error
                          (Design.Decl.NF term)
      nf (Let _ value rest prf)
        = case Proofs.Function.nf value of
            Right prfM => do prfR <- Design.nf rest
                             pure (DeclM prfM prfR)

            Left _ =>
              case Function.Default.nf value of
                Right prfM => do prfR <- Design.nf rest
                                 pure (DeclMP prfM prfR)

                Left _ =>
                  do prfD <- DataType.nf value
                     prfR <- Design.nf rest
                     pure (DeclD prfD prfR)

      nf term = Left (Err (getFC term) InvalidDesignDecl)

-- [ EOF ]
