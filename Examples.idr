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
  Func (Func (Func (Func EndModule)))

||| This is how we can *bind* it to a name.
public export
example001 : SystemV Nil Example000_Ty
example001 =
    Let (TyFunc (TyParam TyLogic)
                (TyFunc (TyPort TyLogic IN)
                        (TyFunc (TyPort TyLogic OUT)
                                (TyFunc (TyPort TyLogic OUT)
                                        TyModule
                                )
                        )
                )
        )
        example000
        (ChkFunc ChkParam
                 (ChkFunc ChkPort
                          (ChkFunc ChkPort
                                   (ChkFunc ChkPort ChkModule))))
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
  Let (TyFunc (TyPort TyLogic IN)
              (TyFunc (TyPort TyLogic OUT)
                      TyModule))
      (Func (Func EndModule))
      (ChkFunc ChkPort
               (ChkFunc ChkPort ChkModule))
      -- module Outer (input wire logic i, output wire logic o);
      (Let (TyFunc (TyPort TyLogic IN)
              (TyFunc (TyPort TyLogic OUT)
                      TyModule))
           -- instantiating a module, unnamed.
           (Func (Func (App (App (Var (T (T H))) (Var (T H))) (Var H))))
           (ChkFunc ChkPort
               (ChkFunc ChkPort ChkModule))
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
  Let (TyFunc (TyPort TyLogic OUT) TyModule)
      (Func EndModule)
      (ChkFunc ChkPort ChkModule)
      -- module Bob (input wire logic o);
      (Let (TyFunc (TyPort TyLogic IN) TyModule)
           (Func EndModule)
           (ChkFunc ChkPort ChkModule)
           -- wire logic chan
           (Let (TyChan TyLogic)
                (MkChan TyLogic)
                (ChkChan)
                -- Alice a(.o(chan))
                (Let TyModule
                     (App (Var (T (T H))) (WriteTo (Var H)))
                     ChkModule
                     -- Bob   b(.i(chan));
                     (Let TyModule
                          (App (Var (T (T H))) (ReadFrom (Var (T H))))
                          ChkModule
                          -- Body of outer
                          EndModule
                     )
                 )
            )
      )
-- --------------------------------------------------------------------- [ EOF ]
