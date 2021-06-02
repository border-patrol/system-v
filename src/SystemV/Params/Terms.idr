||| Terms in SystemV.Params.
|||
module SystemV.Params.Terms

import public SystemV.Common.Types.Gate
import public SystemV.Params.Types

%default total

namespace Params
  public export
  data SystemV : Context lvls -> TYPE level -> Type where

    -- [ Types ]

    DATATYPE : (fc : FC) -> SystemV ctxt DATATYPE

    -- Unit
    TyUnit : (fc : FC) -> SystemV ctxt UnitTyDesc
    TyNat  : (fc : FC) -> SystemV ctxt NatTyDesc
    TyBool : (fc : FC) -> SystemV ctxt BoolTyDesc

    -- Hardware Specific Constructs
    TyModule : (fc : FC) -> SystemV ctxt ModuleTyDesc

    TyChan : (fc : FC)
          -> (typeD : SystemV ctxt DATATERM)
                   -> SystemV ctxt ChanTyDesc

    TyPort : (fc : FC)
          -> (desc : SystemV ctxt DATATERM)
          -> (dir  : Direction)
                  -> SystemV ctxt (PortTyDesc dir)

    -- Data types
    TyLogic : (fc : FC) -> SystemV ctxt DATATERM

    TyVect : (fc : FC)
          -> (size : SystemV ctxt NatTy)
          -> (typeE : SystemV ctxt DATATERM)
          -> SystemV ctxt DATATERM

    -- [ Terms ]

    -- STLC
    Var : {u : Universe}
       -> {type : TYPE u}
       -> (fc : FC)
       -> (idx : Elem Universe TYPE type ctxt)
              -> SystemV ctxt type

    Func : {paramTyDesc     : TYPE (IDX TYPE)}
        -> {paramTy, bodyTy : TYPE (IDX TERM)}

        -> (fc : FC)
        -> (type : SystemV  ctxt    paramTyDesc)
        -> (body : SystemV (ctxt +=             paramTy) bodyTy)

        -> (chk  : Types.TyCheck paramTyDesc paramTy)
        -> (prf  : Function.ValidTerm (IDX TERM) (FuncTy paramTy bodyTy))

                -> SystemV  ctxt        (FuncTy paramTy  bodyTy)

    App : {paramTy, bodyTy : TYPE (IDX TERM)}

       -> (fc : FC)
       -> (func  : SystemV ctxt (FuncTy paramTy  bodyTy))
       -> (value : SystemV ctxt         paramTy)
                -> SystemV ctxt                   bodyTy

    -- STLC with Defaults
    FuncParam : {uty, utm : Universe}
             -> {typeA : TYPE uty}
             -> {termA : TYPE utm}
             -> {bodyTy      : TYPE (IDX TERM)}

             -> (fc : FC)
             -> (type : SystemV  ctxt    typeA)
             -> (def  : SystemV  ctxt    termA)
             -> (body : SystemV (ctxt += termA) bodyTy)

             -> (prf  : Function.ValidTerm (IDX TERM) (FuncParamTy utm termA bodyTy))
             -> (chk  : Default.TyCheck uty utm typeA termA)
                     -> SystemV  ctxt        (FuncParamTy utm termA bodyTy)


    AppDef : {utm     : Universe}
          -> {term    : TYPE utm}
          -> {bodyTy  : TYPE (IDX TERM)}
          -> (fc : FC)
          -> (func    : SystemV ctxt (FuncParamTy utm term bodyTy))
                     -> SystemV ctxt                       bodyTy

    AppOver : {utm    : Universe}
           -> {term   : TYPE utm}
           -> {bodyTy : TYPE (IDX TERM)}

           -> (fc : FC)
           -> (fun : SystemV ctxt (FuncParamTy utm term bodyTy))
           -> (arg : SystemV ctxt term)
                  -> SystemV ctxt                       bodyTy


    -- Unit

    MkUnit : (fc : FC) -> SystemV ctxt UnitTy

    -- Hardware specific

    EndModule : (fc : FC) -> SystemV ctxt ModuleTy

    MkPort : (fc : FC)
          -> (typeD : SystemV ctxt DATATERM)

          -> (dir   : Direction)
                   -> SystemV ctxt (PortTy dir)

    MkChan : (fc : FC)
          -> (typeD : SystemV ctxt DATATERM)
                   -> SystemV ctxt ChanTy

    WriteTo : (fc : FC)
           -> (chan : SystemV ctxt ChanTy)
                   -> SystemV ctxt (PortTy OUT)

    ReadFrom : (fc : FC)
            -> (chan : SystemV ctxt ChanTy)
                    -> SystemV ctxt (PortTy IN)

    Drive : (fc : FC)
         -> (chan : SystemV ctxt (PortTy OUT))
                 -> SystemV ctxt UnitTy

    Catch : (fc : FC)
         -> (chan : SystemV ctxt (PortTy IN))
                 -> SystemV ctxt UnitTy

    -- Runtime wiring decisions
    IfThenElseR : (fc : FC)
               -> (test     : SystemV ctxt (PortTy IN))
               -> (whenIsZ  : SystemV ctxt UnitTy)
               -> (whenNotZ : SystemV ctxt UnitTy)
                           -> SystemV ctxt UnitTy

    -- Connect two ports together.
    Connect : {dirL, dirR : Direction}

           -> (fc : FC)
           -> (portL : SystemV ctxt (PortTy dirL))
           -> (portR : SystemV ctxt (PortTy dirR))
           -> (prf   : ValidFlow dirL dirR)
                    -> SystemV ctxt UnitTy

    -- Casts
    Cast : {dirA  : Direction}

        -> (fc : FC)
        -> (portA : SystemV ctxt (PortTy dirA))
        -> (type  : SystemV ctxt DATATERM)

        -> (dirB  : Direction)
        -> (prf   : ValidCast (PortTy dirA)
                              (PortTy dirB))
                 -> SystemV ctxt (PortTy dirB)


    -- Operations on Data.
    Slice : (fc : FC)
         -> (port  : SystemV ctxt (PortTy dir))
         -> (alpha : SystemV ctxt (NatTy))
         -> (omega : SystemV ctxt (NatTy))
                  -> SystemV ctxt (PortTy dir)

    Index : {dir   : Direction}

         -> (fc : FC)
         -> (idx  : SystemV ctxt (NatTy))
         -> (port : SystemV ctxt (PortTy dir))
                 -> SystemV ctxt (PortTy dir)

    Size : {dir   : Direction}

        -> (fc : FC)
        -> (port : SystemV ctxt (PortTy dir))
                -> SystemV ctxt (NatTy)

    -- Gates
    Not : (fc : FC)
       -> (portO : SystemV ctxt (PortTy OUT))
       -> (portI : SystemV ctxt (PortTy IN))
                -> SystemV ctxt UnitTy

    Gate : (fc : FC)
        -> (kind          : GateKind)
        -> (portO         : SystemV ctxt (PortTy OUT))
        -> (portIA,portIB : SystemV ctxt (PortTy IN))
                         -> SystemV ctxt UnitTy


    -- [ Binders ]

    Let : {typeU     : Universe}
       -> {typeValue : TYPE typeU}
       -> {typeBody  : TYPE (IDX TERM)}

       -> (fc : FC)
       -> (value : SystemV  ctxt    typeValue)
       -> (body  : SystemV (ctxt += typeValue) typeBody)
       -> (prf   : ValidBind typeU typeValue)
                -> SystemV  ctxt               typeBody

    -- [ Sequencing ]

    Seq : {type : TYPE (IDX TERM)}

       -> (fc : FC)
       -> (left  : SystemV ctxt UnitTy)
       -> (right : SystemV ctxt type)
       -> (prf   : ValidSeq (IDX TERM) type)
                -> SystemV ctxt type

    -- Nats & Bools
    MkNat  : (fc : FC) -> (n : Nat) -> SystemV ctxt NatTy
    MkBool : (fc : FC) -> (b : Bool) -> SystemV ctxt BoolTy

    -- Compile Time
    IfThenElseC : (fc : FC)
               -> (test     : SystemV ctxt BoolTy)
               -> (whenIsZ  : SystemV ctxt UnitTy)
               -> (whenNotZ : SystemV ctxt UnitTy)
                           -> SystemV ctxt UnitTy

    -- [ NatOpts ]
    NatOpArith : (fc : FC)
              -> (op : ArithOp)
              -> (left  : SystemV ctxt NatTy)
              -> (right : SystemV ctxt NatTy)
                       -> SystemV ctxt NatTy

    NatOpCmp : (fc : FC)
            -> (op : CompOp)
            -> (left,right : SystemV ctxt NatTy)
                          -> SystemV ctxt BoolTy

    BoolOpBin : (fc : FC)
             -> (op : BoolBinOp)
             -> (left  : SystemV ctxt BoolTy)
             -> (right : SystemV ctxt BoolTy)
                      -> SystemV ctxt BoolTy

    BoolNot : (fc : FC)
           -> (bool : SystemV ctxt BoolTy)
                   -> SystemV ctxt BoolTy

    -- [ For ]
    --
    --  It is just sequences of applications.
    --
    For : (fc : FC)
       -> (counter : SystemV ctxt NatTy)
       -> (body    : SystemV (ctxt += NatTy) UnitTy)
                  -> SystemV ctxt UnitTy

export
getFC : SystemV ctxt type -> FC
getFC (DATATYPE fc)                          = fc
getFC (TyUnit fc)                            = fc
getFC (TyNat fc)                             = fc
getFC (TyBool fc)                            = fc
getFC (TyModule fc)                          = fc
getFC (TyChan fc typeD)                      = fc
getFC (TyPort fc desc dir)                   = fc
getFC (TyLogic fc)                           = fc
getFC (TyVect fc size typeE)                 = fc
getFC (Var fc idx)                           = fc
getFC (Func fc x body chk prf)               = fc
getFC (App fc func value)                    = fc
getFC (FuncParam fc x def body prf chk)      = fc
getFC (AppDef fc func)                       = fc
getFC (AppOver fc fun arg)                   = fc
getFC (MkUnit fc)                            = fc
getFC (EndModule fc)                         = fc
getFC (MkPort fc typeD dir)                  = fc
getFC (MkChan fc typeD)                      = fc
getFC (WriteTo fc chan)                      = fc
getFC (ReadFrom fc chan)                     = fc
getFC (Drive fc chan)                        = fc
getFC (Catch fc chan)                        = fc
getFC (IfThenElseR fc test whenIsZ whenNotZ) = fc
getFC (Connect fc portL portR prf)           = fc
getFC (Cast fc portA x dirB prf)             = fc
getFC (Slice fc port alpha omega)            = fc
getFC (Index fc idx port)                    = fc
getFC (Size fc port)                         = fc
getFC (Not fc portO portI)                   = fc
getFC (Gate fc kind portO portIA portIB)     = fc
getFC (Let fc value body prf)                = fc
getFC (Seq fc left right prf)                = fc
getFC (MkNat fc n)                           = fc
getFC (MkBool fc b)                          = fc
getFC (IfThenElseC fc test whenIsZ whenNotZ) = fc
getFC (NatOpArith fc op left right)          = fc
getFC (NatOpCmp fc op left right)            = fc
getFC (BoolOpBin fc op left right)           = fc
getFC (BoolNot fc bool)                      = fc
getFC (For fc counter body)                  = fc

-- [ EOF ]
