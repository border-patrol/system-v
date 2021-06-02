module SystemV.HigherOrder.Terms.NormalForm.Proofs

import Toolkit.Decidable.Do
import Toolkit.Decidable.Informative

import SystemV.Common.Utilities
import SystemV.HigherOrder.Types
import SystemV.HigherOrder.Terms

import SystemV.HigherOrder.Terms.NormalForm.Error
import SystemV.HigherOrder.Terms.NormalForm.Types

%default total

namespace DataType
  export
  nf : (term : SystemV ctxt type) -> Either NormalForm.Error (DataType.NF term)
  nf (Var idx) = Right TyRef
  nf TyLogic = Right TyLogic
  nf (TyVect s typeE)
    = do prf <- nf typeE
         pure (TyVect prf)


  nf _ = Left IsNotDataType

namespace TermType
  export
  nf : (term : SystemV ctxt type)
            -> Either NormalForm.Error
                      (TermType.NF term)
  nf TyModule = Right TyModule
  nf TyUnit   = Right TyUnit
  nf (TyChan ty)
    = do prf <- DataType.nf ty
         pure (TyChan prf)

  nf (TyPort ty dir)
    = do prf <- DataType.nf ty
         pure (TyPort prf)

  nf (TyFunc param return prf)
    = do p <- TermType.nf param
         r <- TermType.nf return
         pure (TyFunc p r)

  nf _ = Left IsNotTermType

namespace Port
  namespace Argument
    export
    nf : (term : SystemV ctxt type)
              -> Either NormalForm.Error
                        (Port.Argument.NF term)

    nf (Var idx) = Right Var
    nf (WriteTo port)
      = do prf <- Port.Argument.nf port
           pure (WriteTo prf)

    nf (ReadFrom port)
      = do prf <- Port.Argument.nf port
           pure (ReadFrom prf)

    nf (Cast port prf)
      = do prf <- Port.Argument.nf port
           pure (Cast prf)

    nf (Slice port alpha omega prf)
      = do prf <- Port.Argument.nf port
           pure (Slice prf)

    nf (Index idx port prf)
      = do prf <- Port.Argument.nf port
           pure (Index prf)

    nf _ = Left InvalidPortArgument


namespace Chan
  export
  nf : (term : SystemV ctxt type)
            -> Either NormalForm.Error
                      (Chan.NF term)
  nf (MkChan ty)
    = do prf <- DataType.nf ty
         pure (MkChan prf)

  nf _ = Left InvalidMkChan

namespace Gate
  export
  nf : (term : SystemV ctxt type)
            -> Either NormalForm.Error
                      (Gate.NF term)
  nf (Not portO portI)
    = do po <- Port.Argument.nf portO
         pi <- Port.Argument.nf portI
         pure (Not po pi)

  nf (Gate kind portO portIA portIB)
    = do po <- Port.Argument.nf portO
         pi <- Port.Argument.nf portIA
         pj <- Port.Argument.nf portIB
         pure (Gate po pi pj)

  nf _ = Left InvalidGate

mutual
  namespace Function
    export
    nf : (term : SystemV ctxt type)
              -> Either NormalForm.Error
                        (Function.NF term)
    nf (Func ty body prf vld)
      = do prfT <- TermType.nf ty
           prfB <- Function.Body.nf body
           pure (Func prfT prfB)
    nf _ = Left InvalidFunc

    namespace Argument
      export
      nf : (term : SystemV ctxt type)
                -> Either NormalForm.Error
                          (Function.Argument.NF term)
      nf MkUnit = Right MkUnit
      nf term
        = do prf <- Port.Argument.nf term
             pure (Var prf)


    namespace Body
      export
      nf : (term : SystemV ctxt type)
                -> Either NormalForm.Error
                          (Function.Body.NF term)

      nf (Func x body prf vld)
        = do prf <- Function.nf (Func x body prf vld)
             pure (IsFunc prf)

      nf EndModule = Right IsEmpty

      nf (Let value body prf)
        = do prf <- Function.Body.Let.nf (Let value body prf)
             pure (IsLet prf)

      nf (Seq left right prf)
        = do prf <- Sequence.nf (Seq left right prf)
             pure (IsSeq prf)

      nf _ = Left InvalidFuncBody

      namespace Let

        export
        nf : (term : SystemV ctxt type)
                  -> Either NormalForm.Error
                               (Function.Body.Let.NF term)
        nf (Let value body prf)
          = case DataType.nf value of
              Right v => do r <- Function.Body.nf body
                            pure (DeclD v r)

              Left _ =>
                case Function.nf value of
                  Right v => do r <- Function.Body.nf body
                                pure (DeclM v r)

                  Left _ =>
                    case Chan.nf value of
                      Right v => do r <- Function.Body.nf body
                                    pure (InstW v r)

                      Left _ => do v <- Application.nf value
                                   r <- Function.Body.nf body
                                   pure (InstM v r)

        nf _ = Left InvalidFuncLet

      namespace Sequence

        export
        nf : (term : SystemV ctxt type)
                  -> Either NormalForm.Error
                            (Sequence.NF term)

        nf EndModule = Right EndModule
        nf MkUnit    = Right MkUnit

        nf (Drive chan)
          = do prf <- Port.Argument.nf chan
               pure (Drive prf)

        nf (Catch chan)
          = do prf <- Port.Argument.nf chan
               pure (Catch prf)

        nf (IfThenElseR test whenIsZ whenNotZ)
          = do prf <- Conditional.nf (IfThenElseR test whenIsZ whenNotZ)
               pure (Cond prf)

        nf (Connect portL portR prf)
          = do prfL <- Port.Argument.nf portL
               prfR <- Port.Argument.nf portR
               pure (Connect prfL prfR)

        nf (Not portO portI)
          = do prf <- Gate.nf (Not portO portI)
               pure (Gate prf)
        nf (Gate kind portO portIA portIB)
          = do prf <- Gate.nf (Gate kind portO portIA portIB)
               pure (Gate prf)

        nf (Let value body prf)
          = do prf <- Function.Body.Let.nf (Let value body prf)
               pure (IsLet prf)

        nf (Seq left right prf)
          = do l <- Sequence.nf left
               r <- Sequence.nf right
               pure (Seq l r)

        nf _ = Left InvalidSeq

      namespace Conditional
        export
        nf : (term : SystemV ctxt type)
                  -> Either NormalForm.Error
                            (Conditional.NF term)
        nf (IfThenElseR test true false)
          = do prfP <- Port.Argument.nf test
               prfT <- Function.Body.nf true
               prfF <- Function.Body.nf false
               pure (IfThenElse prfP prfT prfF)
        nf _ = Left InvalidConditional

  namespace Application

    export
    nf : (term : SystemV ctxt type)
              -> Either NormalForm.Error
                        (Application.NF term)
    nf (App (Var ref) param)
      = do prf <- Function.Argument.nf param
           pure (AppRef prf)
    nf (App func param)
      = do f <- Application.nf func
           p <- Function.Argument.nf param
           pure (AppRec f p)

    nf _ = Left InvalidApp


namespace Design
  mutual

    export
    nf : (term : SystemV ctxt type)
              -> Either NormalForm.Error
                        (Design.NF term)
    nf (App func MkUnit)
      = do prf <- Application.nf (App func MkUnit)
           pure (IsTop prf)

    nf (Let value body prf)
      = do prf <- Design.Decl.nf (Let value body prf)
           pure (IsDecl prf)

    nf _ = Left InvalidDesignBody

    namespace Decl
      export
      nf : (term : SystemV ctxt type)
                -> Either NormalForm.Error
                          (Design.Decl.NF term)
      nf (Let value rest prf)
        = case Function.nf value of
            Right prfM => do prfR <- Design.nf rest
                             pure (DeclM prfM prfR)

            Left err => do prfD <- DataType.nf value
                           prfR <- Design.nf rest
                           pure (DeclD prfD prfR)

      nf _ = Left InvalidDesignDecl

-- [ EOF ]
