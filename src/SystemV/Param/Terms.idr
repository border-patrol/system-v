||| Terms in SystemV.Param.
|||
module SystemV.Param.Terms

-- import SystemV.Common.Utilities

import public SystemV.Common.Types.Gate
import public SystemV.Param.Types

%default total


-- @TODO-TODO Add restrictions on let's

namespace Param
  public export
  data SystemV : Context lvls -> TYPE level -> Type where
    -- [ Types ]

    DATATYPE : SystemV ctxt DATATYPE

    -- Unit
    TyUnit : SystemV ctxt UnitTyDesc
    TyNat  : SystemV ctxt NatTyDesc
    TyBool : SystemV ctxt BoolTyDesc

    -- Hardware Specific Constructs
    TyModule : SystemV ctxt ModuleTyDesc

    TyChan : (typeD : SystemV ctxt DATATERM)
                   -> SystemV ctxt ChanTyDesc

    TyPort : (desc : SystemV ctxt DATATERM)
          -> (dir  : Direction)
                  -> SystemV ctxt (PortTyDesc dir)

    -- Data types
    TyLogic : SystemV ctxt DATATERM

    TyVect : (size : SystemV ctxt NatTy)
          -> (typeE : SystemV ctxt DATATERM)
          -> SystemV ctxt DATATERM

    -- [ Terms ]

    -- STLC
    Var : {u : Universe}
       -> {type : TYPE u}
       -> (idx : Elem Universe TYPE type ctxt)
              -> SystemV ctxt type

    Func : {paramTyDesc     : TYPE (IDX TYPE)}
        -> {paramTy, bodyTy : TYPE (IDX TERM)}

        -> (type : SystemV  ctxt    paramTyDesc)
        -> (body : SystemV (ctxt +=             paramTy) bodyTy)

        -> (chk  : Types.TyCheck paramTyDesc paramTy)
        -> (prf  : Function.ValidTerm (IDX TERM) (FuncTy paramTy bodyTy))

                -> SystemV  ctxt        (FuncTy paramTy  bodyTy)

    App : {paramTy, bodyTy : TYPE (IDX TERM)}

       -> (func  : SystemV ctxt (FuncTy paramTy  bodyTy))
       -> (value : SystemV ctxt         paramTy)
                -> SystemV ctxt                   bodyTy

    -- STLC with Defaults
    FuncParam : {uty, utm : Universe}
             -> {typeA : TYPE uty}
             -> {termA : TYPE utm}
             -> {bodyTy      : TYPE (IDX TERM)}

             -> (type : SystemV  ctxt    typeA)
             -> (def  : SystemV  ctxt    termA)
             -> (body : SystemV (ctxt += termA) bodyTy)

             -> (prf  : Function.ValidTerm (IDX TERM) (FuncParamTy utm termA bodyTy))
             -> (chk  : Default.TyCheck uty utm typeA termA)
                     -> SystemV  ctxt        (FuncParamTy utm termA bodyTy)


    AppDef : {utm     : Universe}
          -> {term    : TYPE utm}
          -> {bodyTy  : TYPE (IDX TERM)}
          -> (func    : SystemV ctxt (FuncParamTy utm term bodyTy))
                     -> SystemV ctxt                       bodyTy

    AppOver : {utm    : Universe}
           -> {term   : TYPE utm}
           -> {bodyTy : TYPE (IDX TERM)}

           -> (fun : SystemV ctxt (FuncParamTy utm term bodyTy))
           -> (arg : SystemV ctxt term)
                  -> SystemV ctxt                       bodyTy


    -- Unit

    MkUnit : SystemV ctxt UnitTy

    -- Hardware specific

    EndModule : SystemV ctxt ModuleTy

    MkPort : (typeD : SystemV ctxt DATATERM)

          -> (dir   : Direction)
                   -> SystemV ctxt (PortTy dir)

    MkChan : (typeD : SystemV ctxt DATATERM)
                   -> SystemV ctxt ChanTy

    WriteTo : (chan : SystemV ctxt ChanTy)
                   -> SystemV ctxt (PortTy OUT)

    ReadFrom : (chan : SystemV ctxt ChanTy)
                    -> SystemV ctxt (PortTy IN)

    Drive : (chan : SystemV ctxt (PortTy OUT))
                 -> SystemV ctxt UnitTy

    Catch : (chan : SystemV ctxt (PortTy IN))
                 -> SystemV ctxt UnitTy

    -- Runtime wiring decisions
    IfThenElseR : (test     : SystemV ctxt (PortTy IN))
               -> (whenIsZ  : SystemV ctxt UnitTy)
               -> (whenNotZ : SystemV ctxt UnitTy)
                           -> SystemV ctxt UnitTy

    -- Connect two ports together.
    Connect : {dirL, dirR : Direction}

           -> (portL : SystemV ctxt (PortTy dirL))
           -> (portR : SystemV ctxt (PortTy dirR))
           -> (prf   : ValidFlow dirL dirR)
                    -> SystemV ctxt UnitTy

    -- Casts
    Cast : {dirA  : Direction}

        -> (portA : SystemV ctxt (PortTy dirA))

        -> (dirB  : Direction)
        -> (prf   : ValidCast (PortTy dirA)
                              (PortTy dirB))
                 -> SystemV ctxt (PortTy dirB)


    -- Operations on Data.
    Slice : (port  : SystemV ctxt (PortTy dir))
         -> (alpha : SystemV ctxt (NatTy))
         -> (omega : SystemV ctxt (NatTy))
                  -> SystemV ctxt (PortTy dir)

    Index : {dir   : Direction}

         -> (idx  : SystemV ctxt (NatTy))
         -> (port : SystemV ctxt (PortTy dir))
                 -> SystemV ctxt (PortTy dir)

    Size : {dir   : Direction}

        -> (port : SystemV ctxt (PortTy dir))
                -> SystemV ctxt (NatTy)

    -- Gates
    Not : (portO : SystemV ctxt (PortTy OUT))
       -> (portI : SystemV ctxt (PortTy IN))
                -> SystemV ctxt UnitTy

    Gate : (kind          : GateKind)
        -> (portO         : SystemV ctxt (PortTy OUT))
        -> (portIA,portIB : SystemV ctxt (PortTy IN))
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

    -- Nats & Bools
    MkNat  : (n : Nat) -> SystemV ctxt NatTy
    MkBool : (b : Bool) -> SystemV ctxt BoolTy

    -- Compile Time
    IfThenElseC : (test     : SystemV ctxt BoolTy)
               -> (whenIsZ  : SystemV ctxt UnitTy)
               -> (whenNotZ : SystemV ctxt UnitTy)
                           -> SystemV ctxt UnitTy

    -- [ NatOpts ]
    NatOpArith : (op : ArithOp)
              -> (left  : SystemV ctxt NatTy)
              -> (right : SystemV ctxt NatTy)
                       -> SystemV ctxt NatTy

    NatOpCmp : (op : CompOp)
            -> (left,right : SystemV ctxt NatTy)
                          -> SystemV ctxt BoolTy

    BoolOpBin : (op : BoolBinOp)
             -> (left  : SystemV ctxt BoolTy)
             -> (right : SystemV ctxt BoolTy)
                      -> SystemV ctxt BoolTy

    BoolNot : (bool : SystemV ctxt BoolTy) -> SystemV ctxt BoolTy

    -- [ For ]
    --
    --  It is just sequences of applications.
    --
    For : (counter : SystemV ctxt NatTy)
       -> (body    : SystemV ctxt (FuncParamTy (IDX TERM) NatTy UnitTy))
                  -> SystemV ctxt UnitTy

-- --------------------------------------------------------------------- [ EOF ]
