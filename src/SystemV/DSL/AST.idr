module SystemV.DSL.AST

import Toolkit.Data.Location

import SystemV.Types

%default total

public export
data AST : Type where
  ||| Names will be converted to De Bruijn indicies.
  Ref : FileContext -> String -> AST

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

  ||| Vectors
  |||
  ||| ```
  ||| <type>[<size>] ::= TyVect size type
  ||| ```
  TyVect : (fc   : FileContext)
        -> (s    : Nat)
        -> (type : AST)
                -> AST

  ||| TypeDefs are just specalised let bidnings
  |||
  ||| ```
  ||| typedef <type def> <name>; <body> ::= TypeDef <type def> <body>
  ||| ```
  |||
  TypeDef : (fc   : FileContext)
         -> (name : String)
         -> (type : AST)
         -> (body : AST)
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
  ||| Logically, we expect flow to be left to right, but to module SystemVerilog assignment we reverse this.
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

  TyParam : AST
  ||| Parameter creation.
  |||
  ||| We will not ask users to bind parameters directly, they won't be
  ||| in the DSL, but we will use sugar to go from the following
  ||| snippet of a module instantiation to collect the parameters
  ||| *and* apply them.
  |||
  ||| ```
  ||| #(<value>,...) ::= MkParan <value>,...
  ||| ```
  |||
  MkParam : (fc  : FileContext)
         -> (val : Nat)
                -> AST

  ||| Boolean Operations on Parameters
  |||
  ||| For example:
  |||
  ||| ```
  ||| (== x y) ::= ParamOpBool (==) x y
  ||| (&& x y) ..
  ||| (|| x y)
  ||| ```
  ParamOpBool : (fc    : FileContext)
             -> (op    : Nat -> Nat -> Bool)
             -> (left  : AST)
             -> (right : AST)
                      -> AST

  ParamOpNot : (fc : FileContext)
            -> (op : AST)
                  -> AST

  ||| Parameter arithmetic
  |||
  ||| ```
  ||| (add x y) ::= ParamOpArith (+) x y
  ||| (sub x y) ...
  ||| (mul x y)
  ||| (div x y)
  ||| ```
  ParamOpArith : (fc    : FileContext)
              -> (op    : Nat -> Nat -> Nat)
              -> (left  : AST)
              -> (right : AST)
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
