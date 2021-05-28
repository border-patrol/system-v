module SystemV.Param.Evaluation.Check

import SystemV.Common.Utilities

import SystemV.Param.Types
import SystemV.Param.Terms


import SystemV.Param.Evaluation.Values
import SystemV.Param.Evaluation.Equality

%default total

public export
data Error = UnexpectedSeq
           | TypeMismatch (SystemV Nil DATATERM) (SystemV Nil DATATERM)

public export
data Check : (type  : SystemV ctxt paramTyDesc)
          -> (prfTy : Value type)
          -> (var   : SystemV  ctxt param)
          -> (prfVa : Value var)
                   -> Type
  where
    VPort  : {tyA,tyB : SystemV Nil DATATERM}
          -> {tyAV : Value tyA}
          -> {tyBV : Value tyB}
          -> (tyA === tyB)
          -> Check (TyPort tyA dir) (TyPort tyAV dir)
                   (MkPort tyB dir) (MkPort tyBV dir)

    VUnit  : {type  : SystemV Nil UnitTyDesc}
          -> {prfTy : Value type}
          -> {var   : SystemV  Nil UnitTy}
          -> {prfVa : Value var}
          -> (czech : TyCheck  UnitTyDesc UnitTy)
          -> (valid : Function.ValidTerm (IDX TERM) (FuncTy UnitTy return))
                   -> Check type prfTy var prfVa

export
check : (type  : SystemV Nil paramTyDesc)
     -> (prfTy : Value type)
     -> (var   : SystemV  Nil param)
     -> (prfVa : Value var)
     -> (czech : TyCheck paramTyDesc param)
     -> (valid : Function.ValidTerm (IDX TERM) (FuncTy param return))
              -> Either Check.Error (Check type prfTy var prfVa)
check {paramTyDesc} {param} type prfTy var prfVa czech valid with (valid)
  check {paramTyDesc = paramTyDesc} {param = (PortTy dir)} type prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) with (czech)
    check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} type prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) with (prfTy)
      check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort tA dir) prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) with (prfVa)
        check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort tA dir) prfTy (MkPort tB dir) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (MkPort tBV dir) with (Data.decEq tA tAV tB tBV)
          check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort tB dir) prfTy (MkPort tB dir) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (MkPort tBV dir) | (Yes Refl)
            = Right (VPort Refl)

          check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort tA dir) prfTy (MkPort tB dir) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (MkPort tBV dir) | (No contra)
            = Left (TypeMismatch tA tB)


        check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort tA dir) prfTy (Seq left right) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (Seq x z)
          = Left UnexpectedSeq


      check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (Seq left right) prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (Seq x z)
        = Left UnexpectedSeq

  check {paramTyDesc = paramTyDesc} {param = UnitTy} type prfTy var prfVa czech valid | (IsValidTerm IsUnitTy y) with (czech)
    check {paramTyDesc = UnitTyDesc} {param = UnitTy} type prfTy var prfVa czech valid | (IsValidTerm IsUnitTy y) | ChkUnit
      = Right (VUnit ChkUnit (IsValidTerm IsUnitTy y))
