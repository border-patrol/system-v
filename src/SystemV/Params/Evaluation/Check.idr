module SystemV.Params.Evaluation.Check

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms


import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Equality

%default total

public export
data Error = TypeMismatch (SystemV Nil DATATERM) (SystemV Nil DATATERM)

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
          -> (DataEq tyA tyB)
          -> Check (TyPort fcA tyA dir) (TyPort tyAV dir)
                   (MkPort fcB tyB dir) (MkPort tyBV dir)

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
      check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort fcA tA dir) prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) with (prfVa)
        check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort fcA tA dir) prfTy (MkPort fcB tB dir) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (MkPort tBV dir) with (Data.decEq tA tAV tB tBV)
          check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort fcA tA dir) prfTy (MkPort fcB tB dir) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (MkPort tBV dir) | (Yes prf)
            = Right (VPort prf)

          check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort fcA tA dir) prfTy (MkPort fcB tB dir) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (MkPort tBV dir) | (No contra)
            = Left (TypeMismatch tA tB)


        check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort _ tA dir) prfTy (Seq _ left right IsUnit) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (Seq x z) impossible
        check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (TyPort _ tA dir) prfTy (Seq _ left right IsMod) prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (TyPort tAV dir) | (Seq x z) impossible


      check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (Seq _ left right IsMod) prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (Seq x z) impossible
      check {paramTyDesc = (PortTyDesc dir)} {param = (PortTy dir)} (Seq _ left right IsMod) prfTy var prfVa czech valid | (IsValidTerm IsPortTy y) | (ChkPort Refl) | (Seq x z) impossible


  check {paramTyDesc = paramTyDesc} {param = UnitTy} type prfTy var prfVa czech valid | (IsValidTerm IsUnitTy y) with (czech)
    check {paramTyDesc = UnitTyDesc} {param = UnitTy} type prfTy var prfVa czech valid | (IsValidTerm IsUnitTy y) | ChkUnit
      = Right (VUnit ChkUnit (IsValidTerm IsUnitTy y))
