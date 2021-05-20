module SystemV.HigherOrder.DSL.AST

import Toolkit.Data.Location

import public SystemV.Common.Types.Direction
import public SystemV.Common.Types.Gate

import public SystemV.Common.Parser.Ref

%default total

public export
data AST : Type where
  ||| Names will be converted to De Bruijn indicies.
  Ref : Ref -> AST

  ||| Module Types are
  |||
  ||| ```
  ||| module <name>(<port decl>*)
  ||| ```
  ||| Names are silently dropped during type checking
  TyFunc : (fc : FileContext)
        -> String
        -> AST
        -> AST
        -> AST
  ||| Modules are functions;
  |||
  ||| ```
  ||| #(parameter <name>,...)(<port decl>); <body>
  |||
  ||| ::=
  |||
  ||| Func TyParam (Func <port decl> <body>)
  |||
  ||| ```
  Func : (fc   : FileContext)
      -> (name : String)
      -> (type : AST)
      -> (body : AST)
              -> AST


  ||| Application is module instantiation.
  |||
  ||| ```
  ||| <func> #(<param>,...)(<chan>,...)
  |||
  ||| ::=
  |||
  ||| App... (App <func> <param>) <chan>...
  ||| ```
  App : (func  : AST)
     -> (param : AST)
              -> AST

  ||| Logic Type
  |||
  ||| ```
  ||| logic ::= TyLogic
  ||| ```
  TyLogic : (fc : FileContext)
               -> AST

  TyModule : AST
  ||| Vectors
  |||
  ||| ```
  ||| <type>[<size>] ::= TyVect size type
  ||| ```
  TyVect : (fc   : FileContext)
        -> (s    : Nat)
        -> (type : AST)
                -> AST

  ||| Ports
  |||
  ||| ```
  ||| <dir> wire <type> ::= TyPort <type> <dir>
  ||| ```
  |||
  TyPort : (fc   : FileContext)
        -> (type : AST)
        -> (dir  : Direction)
                -> AST

  ||| Creating a channel of the given type.
  |||
  ||| We will hide this by hidding it within a let binding.
  ||| So the following:
  |||
  ||| ```
  ||| wire <type> <name>; <body>
  |||
  ||| ::=
  |||
  ||| ```
  ||| let <name> = MkChan <type> in <body>
  ||| ```
  MkChan : (fc   : FileContext)
        -> (type : AST)
                -> AST

  ||| Getting the input from a channel.
  |||
  ||| ```
  ||| (writeTo chan) ::= (WriteTo chan)
  ||| ```
  |||
  WriteTo : (fc   : FileContext)
         -> (chan : AST)
                 -> AST

  ||| Getting the output from a channel.
  |||
  ||| ```
  ||| (readFrom chan) ::= (ReadFrom chan)
  ||| ```
  |||
  ReadFrom : (fc   : FileContext)
          -> (chan : AST)
                  -> AST

  ||| Driving channels
  |||
  ||| ```
  ||| (drive (writeTo chan));
  ||| ```
  Drive : (fc   : FileContext)
       -> (chan : AST)
               -> AST

  ||| Catching channels
  |||
  ||| ```
  ||| (catch (readFrom chan));
  ||| (catch port);
  ||| ```
  Catch : (fc   : FileContext)
       -> (chan : AST)
               -> AST

  ||| Slicing channels
  |||
  ||| ```
  ||| catch chan;
  ||| ```
  Slice : (fc   : FileContext)
       -> (port : AST)
       -> (s,e  : Nat)
               -> AST

  ||| Wiring decisions
  |||
  ||| ```
  ||| if (<test>) begin
  |||    <true>
  ||| end
  ||| else begin
  |||   <false>
  ||| end
  |||
  ||| ::=
  |||
  ||| IfThenElse <test> <true> <false>
  |||
  ||| ```
  |||
  IfThenElse : (fc    : FileContext)
            -> (test  : AST)
            -> (true  : AST)
            -> (false : AST)
                     -> AST

  ||| Connect two ports together.
  |||
  ||| Logically, we expect flow to be left to right, but to module SystemV.Core assignment we reverse this.
  |||
  ||| ```
  ||| assign portR = portL; ::= Connect portL portR
  ||| ```
  Connect : (fc    : FileContext)
         -> (portL : AST)
         -> (portR : AST)
                  -> AST

  ||| Casts are type-directed
  |||
  ||| ```
  ||| (cast <port> <type>)
  ||| ```
  Cast : (fc   : FileContext)
      -> (port : AST)
      -> (type : AST)
      -> (dir  : Direction)
              -> AST

  ||| Binders
  |||
  ||| Bind things to names.
  ||| The things being:
  |||
  ||| ## Modules
  |||
  ||| ```
  ||| module <name> <value>; <body>
  |||
  ||| ::=
  |||
  ||| let <name> = <value> in <body>
  ||| ```
  |||
  ||| ## Channels
  |||
  ||| ```
  ||| wire <type> <name>; <body>
  |||
  ||| ::=
  |||
  ||| let <name> = MkChan <type> in <body>
  ||| ```
  |||
  ||| ## Module instantiations
  |||
  ||| ```
  ||| <value_a> <name> <value_b>; <body>
  |||
  ||| ::=
  |||
  ||| let <name> = App <value_a> <value_b> in <body>
  ||| ```
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

  Index : FileContext -> Nat -> AST -> AST

public export
setFileName : (fname : String)
           -> (ast   : AST)
                    -> AST
setFileName fname (Ref x)
  = Ref (record {span $= setSource fname} x)

setFileName fname (Func fc name type body)
  = Func (setSource fname fc)
         name
         (setFileName fname type)
         (setFileName fname body)

setFileName fname (App func param)
  = App (setFileName fname func)
        (setFileName fname param)

setFileName fname (TyLogic fc)
  = TyLogic (setSource fname fc)

setFileName fname (TyVect fc s type)
  = TyVect (setSource fname fc)
           s
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

setFileName fname (Drive fc chan )
  = Drive (setSource fname fc)
          (setFileName fname chan)

setFileName fname (Catch fc chan)
  = Catch (setSource fname fc)
          (setFileName fname chan)

setFileName fname (Slice fc port s e)
  = Slice (setSource fname fc)
          (setFileName fname port)
          s
          e

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

setFileName fname TyModule
  = TyModule
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
          i
          (setFileName fname p)

setFileName fname (TyFunc fc n a b)
  = TyFunc (setSource fname fc)
           n
           (setFileName fname a)
           (setFileName fname b)

-- [ EOF ]
