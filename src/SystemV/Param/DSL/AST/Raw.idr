module SystemV.Param.DSL.AST.Raw

import Control.WellFounded

import Data.List1

import Toolkit.Data.Location

import SystemV.Common.Parser.Ref

import SystemV.Common.Types.Direction
import SystemV.Common.Types.Gate

import SystemV.Common.Parser.Arithmetic
import SystemV.Common.Parser.Boolean

%default total


public export
data AST : Type where
  Ref : Ref -> AST

  Func : (fc     : FileContext)
      -> (params : List (String, AST, AST))
      -> (ports  : List (String, AST))
      -> (body : AST)
              -> AST

  App : (fc : FileContext)
     -> (func   : AST)
     -> (params : Maybe (List1 (String, AST)))
     -> (ports  : List1 AST)
              -> AST

  TyNat  : (fc : FileContext) -> AST
  TyDATA : (fc : FileContext) -> AST

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

  BExpr : Boolean.Expr -> AST

  AExpr : Arithmetic.Expr -> AST

  For : FileContext -> String -> AST -> AST -> AST


mutual
  setFileNamesParams' : String -> List (String, AST, AST)
                               -> List (String, AST, AST)
  setFileNamesParams' f [] = []
  setFileNamesParams' f ((p,x,y) :: xs)
    = (p, setFileName f x, setFileName f y) :: setFileNamesParams' f xs


  setFileNamesParams : String -> List (String, AST)
                              -> List (String, AST)
  setFileNamesParams f [] = []
  setFileNamesParams f ((p,x) :: xs)
    = (p, setFileName f x) :: setFileNamesParams f xs

  setFileNamesPorts : String -> List AST
                             -> List AST
  setFileNamesPorts f [] = []
  setFileNamesPorts f (x :: xs)
    = setFileName f x :: setFileNamesPorts f xs


  export
  setFileName : (fname : String)
             -> (ast   : AST)
                      -> AST
  setFileName fname (Ref x)
    = Ref (record {span $= setSource fname} x)

  setFileName fname (Func fc params ports body)
    = Func (setSource fname fc)
           (setFileNamesParams' fname params)
           (setFileNamesParams  fname ports)
           (setFileName fname body)

  setFileName fname (App fc func params (port:::ports))
    = let ps = case params of
                 Nothing => Nothing
                 Just ((p,value):::ps')
                   => Just ((p, setFileName fname value) ::: setFileNamesParams fname ps')
      in App (setSource fname fc)
             (setFileName fname func)
             ps
             (setFileName fname port ::: setFileNamesPorts  fname ports)

  setFileName fname (TyNat fc)
    = TyNat (setSource fname fc)

  setFileName fname (TyDATA fc)
    = TyDATA (setSource fname fc)


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

  setFileName fname (BExpr x)
    = BExpr x

  setFileName fname (AExpr x)
    = AExpr x

  setFileName fname (For fc n i b)
     = For (setSource fname fc)
           n
           (setFileName fname i)
           (setFileName fname b)

-- [ EOF ]
