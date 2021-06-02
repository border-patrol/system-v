module SystemV.Params.DSL.AST.Elab

import Decidable.Equality
import Data.List
import Data.List1

import Toolkit.Decidable.Informative
import Toolkit.Data.Location
import Toolkit.Data.List.Subset

import SystemV.Common.Parser.Ref

import SystemV.Common.Types.Direction
import SystemV.Common.Types.Gate
import SystemV.Common.Types.Boolean
import SystemV.Common.Types.Nat.Comparison
import SystemV.Common.Types.Nat.Arithmetic

import SystemV.Common.Parser.Arithmetic
import SystemV.Common.Parser.Boolean

import SystemV.Params.DSL.AST.Raw
import SystemV.Params.DSL.AST

%hide Boolean.Raw.value
%hide SystemV.Common.Parser.Arithmetic.value

%default covering

foldrM : (Monad m)
      => (funcM : a -> b -> m b)
      -> (init  : b)
      -> (input : List a)
               -> m b
foldrM funcM init Nil = pure init
foldrM funcM init (x :: xs)
  = (\z => funcM x z) =<< foldrM funcM init xs

namespace ValidKey
  public export
  data ValidKey : (given : (FileContext, String, Raw.AST))
               -> (exp   : String)
                        -> Type
    where
      IsValid : (prf : given === expected)
                    -> ValidKey (fc, given,val) expected

  export
  data Error = NotSame String String

  export
  Show ValidKey.Error where
    show (NotSame x y) = show x ++ " is not equal to " ++ show y

  notValid : (given = expected -> Void)
          -> ValidKey (fc, given, value) expected
          -> Void
  notValid f (IsValid Refl) = f Refl

  export
  validKey : (given : (FileContext, String, Raw.AST))
          -> (exp   : String)
                   -> DecInfo ValidKey.Error (ValidKey given exp)
  validKey (fc, given, value) expected with (decEq given expected)
    validKey (fc, given, value) expected | (Yes prf)
      = Yes (IsValid prf)
    validKey (fc, given, value) expected | (No contra)
      = No (NotSame given expected) (notValid contra)

FuncSpec : Type
FuncSpec = List String

Env : Type
Env = List (String,FuncSpec)

ext : String -> List (FileContext, String,Raw.AST, Raw.AST) -> Env -> Env
ext x ys = (::) (x,map (fst . snd) ys)

public export
data Error = Err FileContext Elab.Error
           | FuncInlined
           | NotAFunc String
           | ParamErr (Subset.Error ValidKey.Error)

Show e => Show (Subset.Error e) where
  show EmptyThat = "Empty That"
  show (Fail e) = show e
  show (FailThere err) = show err

export
Show Elab.Error where
  show (Err fc err) = show err
  show FuncInlined = "Function presented inlined"
  show (NotAFunc s) = "Function expected given " ++ show s
  show (ParamErr e) = show e


mkArithExpr : Arithmetic.Expr -> Params.AST
mkArithExpr (NatV fc n)
  = MkNat fc n
mkArithExpr (R ref )
  = Ref ref
mkArithExpr (Op fc kind l r)
  = NatOpArith fc kind (mkArithExpr l)
                       (mkArithExpr r)


mkBoolExpr : Boolean.Expr -> Params.AST

mkBoolExpr (NatV fc n)
  = mkArithExpr n

mkBoolExpr (BoolV fc b)
  = (MkBool fc b)

mkBoolExpr (R ref)
  = (Ref ref)

mkBoolExpr (Not fc expr)
  = BoolNot fc (mkBoolExpr expr)

mkBoolExpr (NatCmp fc kind l r)
  = NatOpCmp fc kind (mkBoolExpr l)
                     (mkBoolExpr r)

mkBoolExpr (BoolCmp fc kind l r)
  = BoolOpBin fc kind (mkBoolExpr l)
                      (mkBoolExpr r)
||| Elab starts here
elab : (env : List (String, (List String)))
    -> (raw : Raw.AST)
           -> Either Elab.Error Params.AST

elab env (Func fc params ports body)
    = do b' <- elab env body
         runFold fc env b' params ports
  where
    foldPorts : FileContext
             -> Env
             -> (end    : Params.AST)
             -> (ports  : List (FileContext, String, Raw.AST))
                       -> Either Elab.Error Params.AST
    foldPorts fc env
        = foldrM (foldPort fc env)
      where
        foldPort : FileContext
                -> Env
                -> (nt   : (FileContext, String, Raw.AST))
                -> (rest : Params.AST)
                        -> Either Elab.Error Params.AST
        foldPort fc env (_,n, ty) rest
          = pure (Func fc n !(elab env ty)
                            rest)


    foldParams : FileContext
              -> Env
              -> (end  : Params.AST)
              -> (rest : List (FileContext,String, Raw.AST, Raw.AST))
                      -> Either Elab.Error Params.AST
    foldParams fc env
        = foldrM (foldParam fc env)
      where
        foldParam : FileContext
                 -> Env
                 -> (ntv  : (FileContext, String, Raw.AST, Raw.AST))
                 -> (rest : Params.AST)
                         -> Either Elab.Error Params.AST
        foldParam fc env (_, n, ty, def) rest
          = pure (FuncDef fc n !(elab env ty)
                               !(elab env def)
                               rest)


    runFold : FileContext
           -> Env
           -> (end    : Params.AST)
           -> (params : List (FileContext, String, Raw.AST, Raw.AST))
           -> (ports  : List (FileContext, String, Raw.AST))
                     -> Either Elab.Error Params.AST
    runFold fc _ end [] []
      = pure (Func fc "()" (TyUnit fc) end)

    runFold fc env end [] (x :: xs)
      = foldPorts fc env end (x :: xs)

    runFold fc env end (x :: xs) []
      = foldParams fc env end (x :: xs)

    runFold fc env end (x :: xs) (y :: ys)
      = foldParams fc env !(foldPorts fc env end (y::ys)) (x::xs)

elab env (App fc (Ref ref) params ports)
    = case params of
       Nothing => mkApps env (Ref ref) ports
       (Just (x:::xs)) =>
         case lookup (get ref) env of
           Nothing => Left (Err fc (NotAFunc (get ref)))
           Just spec =>
             case subset validKey (x::xs) spec of
               (No msgWhyNot prfWhyNot) =>
                 Left (Err fc (ParamErr msgWhyNot))

               (Yes prfWhy) =>
                 do acc <- mkAppDefs fc env (Ref ref) (x::xs) spec prfWhy
                    mkApps env acc ports
  where
    mkAppDefs : (fc    : FileContext)
             -> (env   : Env)
             -> (acc : Params.AST)
             -> (ps    : List (FileContext, String, Raw.AST))
             -> (s     : List String)
             -> (prf   : Subset ValidKey ps s)
                      -> Either Elab.Error Params.AST
    mkAppDefs fc env acc [] [] Empty = pure acc

    -- [ NOTE ]
    --
    -- In this case no overridden parameters have been used.
    -- We still need to apply the defaults left.
    mkAppDefs fc env acc [] s EmptyThis
        = foldlM (mkApp' fc) acc s
      where
        mkApp' : FileContext -> Params.AST -> String -> Either Elab.Error Params.AST
        mkApp' fc a _ = pure (AppDef fc a)

    mkAppDefs fc env acc ((fc', _,v) :: xs) (y :: ys) (Keep prf rest)
      = do v' <- elab env v
           mkAppDefs fc env (AppOver fc' acc v') xs ys rest

    mkAppDefs fc env acc ps (_ :: ys) (Skip rest)
      = mkAppDefs fc env (AppDef fc acc) ps ys rest

    mkApps : Env -> Params.AST -> List1 (FileContext, Raw.AST) -> Either Elab.Error Params.AST
    mkApps env start ((fc,head) ::: tail)
        = foldlM (mkApp env) start ((fc, head)::tail)
      where
        mkApp : Env -> Params.AST -> (FileContext, Raw.AST) -> Either Elab.Error Params.AST
        mkApp env p (fc, rest)
          = do r' <- elab env rest
               pure (App fc p r')



elab env (App fc _ params ports)
  = Left (Err fc FuncInlined)

elab env (Let fc name value@(Func _ params _ _) body)
  = do v' <- elab env value
       b' <- elab (ext name params env) body
       pure (Let fc name v' b')

elab env (Let fc name value body)
  = pure (Let fc name !(elab env value)
                      !(elab env body))

elab env (BExpr fc x)
    = pure (mkBoolExpr x)

elab env (AExpr fc x)
    = pure (mkArithExpr x)

elab env (For fc n i body)
  = do i' <- elab env i
       b' <- elab env body
       pure (For fc n i' b')

elab env (Ref x)
  = pure (Ref x)

elab env (TyNat fc)
  = pure (TyNat fc)


elab env (TyDATA fc)
  = pure (TyDATA fc)


elab env (TyLogic fc)
  = pure (TyLogic fc)

elab env (TyVect fc s type)
  = pure (TyVect fc !(elab env s)
                    !(elab env type))

elab env (TyPort fc type dir)
  = pure (TyPort fc !(elab env type)
                    dir)

elab env (MkChan fc type)
  = pure (MkChan fc !(elab env type))

elab env (WriteTo fc chan)
  = pure (WriteTo fc !(elab env chan))

elab env (ReadFrom fc chan)
  = pure (ReadFrom fc !(elab env chan))

elab env (Drive fc chan)
  = pure (Drive fc !(elab env chan))

elab env (Catch fc chan)
  = pure (Catch fc !(elab env chan))

elab env (Slice fc port s e)
  = pure (Slice fc !(elab env port)
                   !(elab env s)
                   !(elab env e))

elab env (IfThenElse fc test true false)
  = pure (IfThenElse fc !(elab env test)
                        !(elab env true)
                        !(elab env false))

elab env (Connect fc portL portR)
  = pure (Connect fc !(elab env portL)
                     !(elab env portR))

elab env (Cast fc port type dir)
  = pure (Cast fc !(elab env port)
                  !(elab env type)
                  dir)

elab env (Seq fc x y)
  = pure (Seq fc !(elab env x)
                 !(elab env y))

elab env (EndModule fc)
  = pure (EndModule fc)

elab env (UnitVal fc)
  = pure (UnitVal fc)

elab env (TyUnit fc)
  = pure (TyUnit fc)

elab env (NotGate fc o i)
  = pure (NotGate fc !(elab env o)
                     !(elab env i))

elab env (Gate fc k o a b)
  = pure (Gate fc k !(elab env o)
                    !(elab env a)
                    !(elab env b))

elab env (Index fc i p)
 = pure (Index fc !(elab env i)
                  !(elab env p))

elab env (Size fc s)
 = pure (Size fc !(elab env s))

namespace Params
  export
  elab : (raw : Raw.AST)
             -> Either Elab.Error Params.AST
  elab = AST.Elab.elab Nil

-- [ EOF ]
