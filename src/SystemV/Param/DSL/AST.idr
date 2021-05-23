module SystemV.Param.DSL.AST

import Toolkit.Data.Location



import public SystemV.Common.Types.Direction
import public SystemV.Common.Types.Gate
import        SystemV.Common.Types.Boolean
import        SystemV.Common.Types.Nat.Comparison
import        SystemV.Common.Types.Nat.Arithmetic

import public SystemV.Common.Parser.Ref
import        SystemV.Common.Parser.Arithmetic
import        SystemV.Common.Parser.Boolean

%default total

namespace Param
  public export
  data AST : Type where
    ||| Names will be converted to De Bruijn indicies.
    Ref : Ref -> AST

    Func : (fc   : FileContext)
        -> (name : String)
        -> (type : AST)
        -> (body : AST)
                -> AST

    App : (func  : AST)
       -> (param : AST)
                -> AST

    FuncDef : (fc   : FileContext)
           -> (name : String)
           -> (type : AST)
           -> (def  : AST)
           -> (body : AST)
                   -> AST

    AppOver : (func  : AST)
           -> (param : AST)
                    -> AST

    AppDef : (func  : AST)
                   -> AST

    TyNat : (fc : FileContext)
          -> AST

    TyDATA : (fc : FileContext)
          -> AST

    TyLogic : (fc : FileContext)
                 -> AST

    TyVect : (fc   : FileContext)
          -> (s    : AST)
          -> (type : AST)
                  -> AST

    TyPort : (fc   : FileContext)
          -> (type : AST)
          -> (dir  : Direction)
                  -> AST

    MkChan : (fc   : FileContext)
          -> (type : AST)
                  -> AST

    WriteTo : (fc   : FileContext)
           -> (chan : AST)
                   -> AST

    ReadFrom : (fc   : FileContext)
            -> (chan : AST)
                    -> AST

    Drive : (fc   : FileContext)
         -> (chan : AST)
                 -> AST

    Catch : (fc   : FileContext)
         -> (chan : AST)
                 -> AST

    Slice : (fc   : FileContext)
         -> (port : AST)
         -> (s,e  : AST)
                 -> AST

    IfThenElse : (fc    : FileContext)
              -> (test  : AST)
              -> (true  : AST)
              -> (false : AST)
                       -> AST

    Connect : (fc    : FileContext)
           -> (portL : AST)
           -> (portR : AST)
                    -> AST

    Cast : (fc   : FileContext)
        -> (port : AST)
        -> (type : AST)
        -> (dir  : Direction)
                -> AST

    Let : (fc    : FileContext)
       -> (name  : String)
       -> (value : AST)
       -> (body  : AST)
                -> AST

    Seq : AST -> AST -> AST
    EndModule : AST
    UnitVal : AST
    TyUnit : AST

    NotGate : FileContext -> AST -> AST -> AST
    Gate : FileContext -> GateKind -> AST -> AST -> AST -> AST

    Index : FileContext -> AST -> AST -> AST

    For : FileContext -> String -> AST -> AST -> AST
    MkNat : FileContext -> Nat -> AST
    MkBool : FileContext -> Bool -> AST

    BoolNot : FileContext -> AST -> AST

    NatOpCmp : FileContext
            -> (op : CompOp)
            -> (l,r : AST)
                  -> AST
    BoolOpBin : FileContext
             -> (op : BoolBinOp)
             -> (l,r : AST)
                    -> AST

    NatOpArith : FileContext
             -> (op : ArithOp)
             -> (l,r : AST)
                    -> AST

public export
setFileName : (fname : String)
           -> (ast   : AST)
                    -> AST
setFileName fname (Ref x)
  = Ref (record {span $= setSource fname} x)

setFileName fname (TyNat fc)
  = TyNat (setSource fname fc)

setFileName fname (TyDATA fc)
  = TyDATA (setSource fname fc)

setFileName fname (NatOpArith fc k l r)
  = NatOpArith (setSource fname fc)
             k
             (setFileName fname l)
             (setFileName fname r)

setFileName fname (BoolOpBin fc k l r)
  = BoolOpBin (setSource fname fc)
             k
             (setFileName fname l)
             (setFileName fname r)

setFileName fname (NatOpCmp fc k l r)
  = NatOpCmp (setSource fname fc)
             k
             (setFileName fname l)
             (setFileName fname r)

setFileName fname (BoolNot fc expr)
  = BoolNot (setSource fname fc)
            (setFileName fname expr)

setFileName fname (MkNat fc n)
  = MkNat (setSource fname fc) n

setFileName fname (MkBool fc n)
  = MkBool (setSource fname fc) n

setFileName fname (Func fc name type body)
  = Func (setSource fname fc)
         name
         (setFileName fname type)
         (setFileName fname body)

setFileName fname (App func param)
  = App (setFileName fname func)
        (setFileName fname param)

setFileName fname (FuncDef fc name type def body)
  = FuncDef (setSource fname fc)
            name
            (setFileName fname type)
            (setFileName fname def)
            (setFileName fname body)

setFileName fname (AppOver func param)
  = AppOver (setFileName fname func)
           (setFileName fname param)

setFileName fname (AppDef func)
  = AppDef (setFileName fname func)


setFileName fname (TyLogic fc)
  = TyLogic (setSource fname fc)

setFileName fname (TyVect fc s type)
  = TyVect (setSource fname fc)
           (setFileName fname s)
           (setFileName fname type)

setFileName fname (TyPort fc type dir)
  = TyPort (setSource fname fc)
           (setFileName fname type)
           dir

setFileName fname (MkChan fc type)
  = MkChan (setSource fname fc)
           (setFileName fname type)

setFileName fname (WriteTo fc chan)
  = WriteTo (setSource fname fc)
            (setFileName fname chan)

setFileName fname (ReadFrom fc chan)
  = ReadFrom (setSource fname fc)
             (setFileName fname chan)

setFileName fname (Drive fc chan)
  = Drive (setSource fname fc)
          (setFileName fname chan)

setFileName fname (Catch fc chan)
  = Catch (setSource fname fc)
          (setFileName fname chan)

setFileName fname (Slice fc port s e)
  = Slice (setSource fname fc)
          (setFileName fname port)
          (setFileName fname s)
          (setFileName fname e)

setFileName fname (IfThenElse fc test true false)
  = IfThenElse (setSource fname fc)
               (setFileName fname test)
               (setFileName fname true)
               (setFileName fname false)

setFileName fname (Connect fc portL portR)
  = Connect (setSource fname fc)
            (setFileName fname portL)
            (setFileName fname portR)

setFileName fname (Cast fc port type dir)
  = Cast (setSource fname fc)
         (setFileName fname port)
         (setFileName fname type)
         dir

setFileName fname (Let fc name value body)
  = Let (setSource fname fc)
        name
        (setFileName fname value)
        (setFileName fname body)

setFileName fname (Seq x y)
  = Seq (setFileName fname x)
        (setFileName fname y)

setFileName fname EndModule
  = EndModule

setFileName fname UnitVal
  = UnitVal
setFileName fname TyUnit
  = TyUnit

setFileName fname (NotGate fc out input)
  = NotGate (setSource fname fc)
            (setFileName fname out)
            (setFileName fname input)

setFileName fname (Gate fc kind out inA inB)
  = Gate (setSource fname fc)
         kind
         (setFileName fname out)
         (setFileName fname inA)
         (setFileName fname inB)

setFileName fname (Index fc i p)
  = Index (setSource fname fc)
          (setFileName fname i)
          (setFileName fname p)

setFileName fname (For fc n i b)
  = For (setSource fname fc)
        n
        (setFileName fname i)
        (setFileName fname b)


-- [ EOF ]
