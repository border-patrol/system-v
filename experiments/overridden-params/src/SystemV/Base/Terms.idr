||| Terms in SystemV.Base.
|||
module SystemV.Base.Terms

-- import SystemV.Common.Utilities

import public SystemV.Common.Types.Gate
import public SystemV.Base.Types

%default total

public export
data SystemV : Context lvls -> TYPE level -> Type where
  -- [ Types ]

  -- STLC
  TyFunc : {paramTYPE, returnTYPE : TYPE (IDX TYPE)}

        -> (paramTy  : SystemV ctxt         paramTYPE)
        -> (returnTy : SystemV ctxt                   returnTYPE)
        -> (vld      : Function.ValidType (IDX TYPE) (FuncTy paramTYPE returnTYPE))
                    -> SystemV ctxt (FuncTy paramTYPE returnTYPE)

  -- Unit
  TyUnit : SystemV ctxt UnitTyDesc
  TyNat  : (n : Nat)
             -> SystemV ctxt (NatTyDesc n)

  -- Hardware Specific Constructs
  TyModule : SystemV ctxt ModuleTyDesc

  TyChan : {type  : TYPE (DATA TYPE)}
        -> (typeD : SystemV ctxt type)
                 -> SystemV ctxt (ChanTyDesc type)

  TyPort : {type : TYPE (DATA TYPE)}
        -> (desc : SystemV ctxt         type)
        -> (dir  : Direction)
                -> SystemV ctxt (PortTyDesc type dir)

  -- Data types
  TyTypeDef : {type : TYPE (DATA TYPE)}
           -> (desc : SystemV ctxt type)
                   -> SystemV ctxt (TypeDefTy type)

  TyLogic : SystemV ctxt LogicTyDesc

  TyVect : (s : Whole)
        -> (typeE : SystemV ctxt type)
        -> SystemV ctxt (VectorTyDesc s type)

  -- [ Terms ]

  -- STLC
  Var : {type : _}
     -> (idx : Elem Universe TYPE type ctxt)
            -> SystemV ctxt type

  Func : {paramTyDesc     : TYPE (IDX TYPE)}
      -> {paramTy, bodyTy : TYPE (IDX TERM)}

      -> (type : SystemV  ctxt    paramTyDesc)
      -> (body : SystemV (ctxt +=             paramTy) bodyTy)

      -> (prf  : TyCheck          paramTyDesc paramTy)
      -> (vld  : Function.ValidTerm (IDX TERM) (FuncTy paramTy bodyTy))

              -> SystemV  ctxt        (FuncTy paramTy  bodyTy)

  App : {paramTy, bodyTy : TYPE (IDX TERM)}

     -> (func  : SystemV ctxt (FuncTy paramTy  bodyTy))
     -> (value : SystemV ctxt         paramTy)
              -> SystemV ctxt                   bodyTy

  -- Unit

  MkUnit : SystemV ctxt UnitTy

  -- Hardware specific

  EndModule : SystemV ctxt ModuleTy

  MkPort : {type  : TYPE (DATA TYPE)}

        -> (typeD : SystemV ctxt type)

        -> (dir   : Direction)
                 -> SystemV ctxt (PortTy type dir)

  MkChan : {type  : TYPE (DATA TYPE)}

        -> (typeD : SystemV ctxt type)
                 -> SystemV ctxt (ChanTy type)

  WriteTo : (chan : SystemV ctxt (ChanTy type))
                 -> SystemV ctxt (PortTy type OUT)

  ReadFrom : (chan : SystemV ctxt (ChanTy type))
                  -> SystemV ctxt (PortTy type IN)

  Drive : {type    : TYPE (DATA TYPE)}

       -> (chan    : SystemV ctxt (PortTy type OUT))
                  -> SystemV ctxt UnitTy

  Catch : {type  : TYPE (DATA TYPE)}

       -> (chan : SystemV ctxt (PortTy type IN))
               -> SystemV ctxt UnitTy

  -- Runtime wiring decisions
  IfThenElseR : {type     : TYPE (DATA TYPE)}

             -> (test     : SystemV ctxt (PortTy type IN))
             -> (whenIsZ  : SystemV ctxt UnitTy)
             -> (whenNotZ : SystemV ctxt UnitTy)
                         -> SystemV ctxt UnitTy

  -- Connect two ports together.
  Connect : {type : TYPE (DATA TYPE)}
         -> {dirL, dirR : Direction}

         -> (portL : SystemV ctxt (PortTy type dirL))
         -> (portR : SystemV ctxt (PortTy type dirR))

         -> (prf   : ValidFlow dirL dirR)
                  -> SystemV ctxt UnitTy

  -- Casts
  Cast : {tyA,tyB : TYPE (DATA TYPE)}
      -> {dirA,dirB : Direction}

      -> (portA : SystemV ctxt (PortTy tyA dirA))

      -> (prf   : ValidCast (PortTy tyA dirA)
                            (PortTy tyB dirB))

               -> SystemV ctxt (PortTy tyB dirB)


  -- Operations on Data.
  Slice : {s     : Whole}
       -> {type  : TYPE (DATA TYPE)}
       -> {a,o   : Nat}

       -> (port  : SystemV ctxt (PortTy (VectorTyDesc s type) dir))
       -> (alpha : SystemV ctxt (NatTy a))
       -> (omega : SystemV ctxt (NatTy o))
       -> (prf   : ValidBound a o s)
                -> SystemV ctxt (PortTy (VectorTyDesc (minus s o a prf) type) dir)

  Index : {i : Nat}
       -> {s : Whole}
       -> {type  : TYPE (DATA TYPE)}
       -> {dir   : Direction}

       -> (idx  : SystemV ctxt (NatTy i))
       -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir))
       -> (prf  : LTE (S i) s)
               -> SystemV ctxt (PortTy type dir)

  Size : {n : Nat}
      -> {type  : TYPE (DATA TYPE)}
      -> {dir   : Direction}

      -> (port : SystemV ctxt (PortTy (VectorTyDesc (W (S n) ItIsSucc) type) dir))
              -> SystemV ctxt (NatTy (S n))

  -- Gates
  Not : {type : TYPE (DATA TYPE)}
     -> (portO : SystemV ctxt (PortTy type OUT))
     -> (portI : SystemV ctxt (PortTy type IN))
              -> SystemV ctxt UnitTy

  Gate : {type : TYPE (DATA TYPE)}

      -> (kind          : GateKind)
      -> (portO         : SystemV ctxt (PortTy type OUT))
      -> (portIA,portIB : SystemV ctxt (PortTy type IN))
                       -> SystemV ctxt UnitTy


  -- [ Binders ]

  Let : {typeU,typeB : Universe}
     -> {typeValue   : TYPE typeU}
     -> {typeBody    : TYPE typeB}

     -> (value : SystemV  ctxt    typeValue)
     -> (body  : SystemV (ctxt += typeValue) typeBody)
              -> SystemV  ctxt               typeBody

  -- [ Sequencing ]

  Seq : {level : Level}
     -> {type : TYPE (IDX level)}

     -> (left  : SystemV ctxt UnitTy)
     -> (right : SystemV ctxt type)
              -> SystemV ctxt type

  MkNat : (n : Nat) -> SystemV ctxt (NatTy n)

-- [ For ]
--
--  It is just sequences of applications.
--
--  For : {n : Nat}
--     -> (counter : SystemV ctxt (NatTy n))
--     -> (body    : SystemV ctxt (FuncTy (NatTy n) UnitTy))
--                -> SystemV ctxt UnitTy

-- --------------------------------------------------------------------- [ EOF ]
