module Examples

import SystemV

%default total

{- [ NOTE ]

In these examples we will look at a simple opaque multiplexer that
routes a signal between one of two wires, and does *something*
depending on the input parameter.

This is how it looks like in SystemVerilog.

```
module switch #( parameter   logic sel)
               ( input wire  logic a
               , output wire logic b
               , output wire logic c);
endmodule
```

This is how it looks like in SystemV-Ascii

```
let switch : Param Logic
          -> Port  Logic Input
          -> Port  Logic Output
          -> Port  Logic Output
          -> Module
     = (fn sel : Param Logic .
           (fn a : Port Logic Input .
               (fn b : Port Logic Input .
                   (fn c : Port Logic Output .
                       EndModule))))
in ...
```
-}

||| A meta type for the function
public export
Example000_Ty : MTy (IDX VALUE)
Example000_Ty
  = (FuncTy (ParamVal LogicTyDesc)
            (FuncTy (PortVal LogicTyDesc IN)
                    (FuncTy (PortVal LogicTyDesc OUT)
                            (FuncTy (PortVal LogicTyDesc OUT)
                                    ModuleTy
                            )
                    )
            )
    )

||| This is how *just* the opaque function will look like.
public export
example000 : SystemV Nil Example000_Ty
example000 =
  Func (TyParam TyLogic)
       (Func (TyPort TyLogic IN)
             (Func (TyPort TyLogic OUT)
                   (Func (TyPort TyLogic OUT)
                         EndModule
                         ChkPort)
                   ChkPort)
             ChkPort)
       ChkParam

||| This is how we can *bind* it to a name.
public export
example001 : SystemV Nil Example000_Ty
example001 =
    Let example000
        (Var H)


{- We now look at other examples -}

||| An empty Top module.
|||
export
top : SystemV Nil ModuleTy
top = EndModule

||| A snippet demonstrating:
|||
||| ```
||| module Inner (input wire logic i, output wire logic o);
||| module Outer (input wire logic i, output wire logic o);
|||  Inner a(.i(i), .o(o));
||| endmodule
||| ```
|||
export
exampleNesting : SystemV Nil
  (FuncTy (PortVal LogicTyDesc IN)
           (FuncTy (PortVal LogicTyDesc OUT)
                                    ModuleTy))
exampleNesting =
  -- module Inner (input wire logic i, output wire logic o);
  Let (Func (TyPort TyLogic IN)
            (Func (TyPort TyLogic OUT)
                  EndModule
                  ChkPort)
            ChkPort)
      -- module Outer (input wire logic i, output wire logic o);
      (Let (Func (TyPort TyLogic IN)
                 (Func (TyPort TyLogic OUT)
                       -- instantiating a module, unnamed.
                       (App (App (Var (T (T H))) (Var (T H))) (Var H))
                       ChkPort)
                 ChkPort)
           (Var (T H)))

||| A snippet demonstrating:
|||
||| ```
||| module Alice (output wire logic o);
||| module Bob   (input  wire logic o);
||| module Outer ();
|||   wire logic chan;
|||   Alice a(.o(chan));
|||   Bob   b(.i(chan));
||| endmodule
||| ```
export
exampleHoriz : SystemV Nil ModuleTy
exampleHoriz =
  -- module Alice (output wire logic o);
  Let (Func (TyPort TyLogic OUT)
            EndModule
            ChkPort)
      -- module Bob (input wire logic o);
      (Let (Func (TyPort TyLogic IN)
                 EndModule
                 ChkPort)
           -- wire logic chan
           (Let (MkChan TyLogic)
                -- Alice a(.o(chan))
                (Let (App (Var (T (T H))) (WriteTo (Var H)))
                     -- Bob   b(.i(chan));
                     (Let (App (Var (T (T H))) (ReadFrom (Var (T H))))
                          -- Body of outer
                          EndModule
                     )
                 )
            )
      )

{- Port level redirects -}

||| The Type
ExampleRedirectTy : MTy (IDX VALUE)
ExampleRedirectTy =
  (FuncTy (PortVal LogicTyDesc OUT)
          (FuncTy (PortVal LogicTyDesc IN)
                  ModuleTy
          )
  )

||| Here we demonstrate port level redirect.
|||
||| ```
||| module Foo(output wire logic o, input wire logic i);
|||   assign o = i;
||| endmodule
||| ```
export
exampleRedirect : SystemV Nil ExampleRedirectTy
exampleRedirect =
  Func (TyPort TyLogic OUT)
       (Func (TyPort TyLogic IN)
             (seq (Connect (Var (T H)) (Var H) FlowOI)
                  EndModule)
             ChkPort)
       ChkPort
-- --------------------------------------------------------------------- [ EOF ]
