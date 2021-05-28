||| Terms in SystemV.Annotated.
|||
module SystemV.Annotated.Terms

-- import SystemV.Common.Utilities

import public SystemV.Common.Types.Gate
import public SystemV.Annotated.Types

%default total

namespace Core
  public export
  data SystemV : Context lvls -> TYPE level -> Type where
    -- [ Types ]

    -- Unit
    TyUnit : SystemV ctxt UnitTyDesc

    -- Hardware Specific Constructs
    TyModule : SystemV ctxt ModuleTyDesc

    TyChan : {type  : TYPE (DATA TYPE)}
          -> (typeD : SystemV ctxt type)
          -> (sense : Sensitivity)
          -> (intent : Intention)
                   -> SystemV ctxt (ChanTyDesc type sense intent)

    TyPort : {type : TYPE (DATA TYPE)}
          -> (desc : SystemV ctxt         type)
          -> (dir  : Direction)
          -> (sense : Sensitivity)
          -> (intent : Intention)
                  -> SystemV ctxt (PortTyDesc type dir sense intent)

    -- Data types
    TyLogic : SystemV ctxt LogicTyDesc

    TyVect : (s     : Whole)
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
          -> (sense : Sensitivity)
          -> (intent : Intention)
                   -> SystemV ctxt (PortTy type dir sense intent)

    MkChan : {type  : TYPE (DATA TYPE)}

          -> (typeD : SystemV ctxt type)
          -> (sense : Sensitivity)
          -> (intent : Intention)
                   -> SystemV ctxt (ChanTy type sense intent)

    WriteTo : (chan : SystemV ctxt (ChanTy type sense intent))
                   -> SystemV ctxt (PortTy type OUT sense intent)

    ReadFrom : (chan : SystemV ctxt (ChanTy type sense intent))
                    -> SystemV ctxt (PortTy type IN  sense intent)

    Drive : {type    : TYPE (DATA TYPE)}
         -> (sense : Sensitivity)
         -> (intent : Intention)
         -> (chan    : SystemV ctxt (PortTy type OUT sense intent))
                    -> SystemV ctxt UnitTy

    Catch : {type  : TYPE (DATA TYPE)}
         -> {sense : Sensitivity}
         -> {intent : Intention}
         -> (chan : SystemV ctxt (PortTy type IN sense intent))
                 -> SystemV ctxt UnitTy

    -- Runtime wiring decisions
    IfThenElseR : {type     : TYPE (DATA TYPE)}
               -> {sense : Sensitivity}
               -> {intent : Intention}

               -> (test     : SystemV ctxt (PortTy type IN sense intent))
               -> (whenIsZ  : SystemV ctxt UnitTy)
               -> (whenNotZ : SystemV ctxt UnitTy)
                           -> SystemV ctxt UnitTy

    -- Connect two ports together.
    Connect : {type : TYPE (DATA TYPE)}
           -> {dirL, dirR : Direction}
           -> {sense : Sensitivity}
           -> {intent : Intention}

           -> (portL : SystemV ctxt (PortTy type dirL sense intent))
           -> (portR : SystemV ctxt (PortTy type dirR sense intent))

           -> (prf   : ValidFlow dirL dirR)
                    -> SystemV ctxt UnitTy

    -- Casts
    Cast : {tyA,tyB : TYPE (DATA TYPE)}
        -> {dirA,dirB : Direction}
        -> {sA,sB : Sensitivity}
        -> {iA,iB : Intention}

        -> (portA : SystemV ctxt (PortTy tyA dirA sA iA))

        -> (prf   : ValidCast (PortTy tyA dirA sA iA)
                              (PortTy tyB dirB sB iB))

                 -> SystemV ctxt (PortTy tyB dirB sB iB)


    -- Operations on Data.
    Slice : {s     : Whole}
         -> {type  : TYPE (DATA TYPE)}

         -> (port  : SystemV ctxt (PortTy (VectorTyDesc s type) dir sense intent))
         -> (alpha : Nat)
         -> (omega : Nat)
         -> (prf   : ValidBound alpha omega s)
                  -> SystemV ctxt (PortTy (VectorTyDesc (minus s omega alpha prf) type) dir sense intent)

    Index : {s : Whole}
         -> {type  : TYPE (DATA TYPE)}
         -> {dir   : Direction}

         -> (idx  : Nat)
         -> (port : SystemV ctxt (PortTy (VectorTyDesc s type) dir sense intent))
         -> (prf  : LTE (S idx) s)
                 -> SystemV ctxt (PortTy type dir sense intent)

    -- Gates
    Not : {type : TYPE (DATA TYPE)}
           -> {sense : Sensitivity}
           -> {intent : Intention}

       -> (portO : SystemV ctxt (PortTy type OUT sense intent))
       -> (portI : SystemV ctxt (PortTy type IN sense intent))
                -> SystemV ctxt UnitTy

    Gate : {type : TYPE (DATA TYPE)}
           -> {sense : Sensitivity}
           -> {intent : Intention}

        -> (kind          : GateKind)
        -> (portO         : SystemV ctxt (PortTy type OUT sense intent))
        -> (portIA,portIB : SystemV ctxt (PortTy type IN  sense intent))
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

-- --------------------------------------------------------------------- [ EOF ]
