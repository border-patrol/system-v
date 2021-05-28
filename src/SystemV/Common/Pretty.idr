module SystemV.Common.Pretty

import public Data.String

import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.Decidable.Equality.Indexed
import Toolkit.Data.Whole

import SystemV.Common.Types.Direction
import SystemV.Common.Types.Gate

import SystemV.Common.Types.Boolean

import SystemV.Common.Types.Nat.Arithmetic
import SystemV.Common.Types.Nat.Comparison

import public SystemV.Common.Parser.Ref
import public SystemV.Common.Parser.Arithmetic
import public SystemV.Common.Parser.Boolean

import SystemV.Common.Sliceable

export
layout : List String -> String
layout = (trim . unlines)

export
prettyHeader : String -> IO ()
prettyHeader s = putStrLn $ unwords ["-- [", s, "] ----------"]


export
Show (Elem u t x xs) where
  show (H y) = "H"
  show (T later) = unwords ["(T", show later <+> ")"]

export
Show Direction where
  show IN = "IN"
  show OUT = "OUT"
  show INOUT = "INOUT"

export
Show Sliceable.Error where
  show (BadBound k j) = "Bad Bound: " ++ "(" ++ show k ++ "," ++ show j ++ ")"
  show (IndexStartsZero k) = "Index must start at zero " ++ show k
  show (IndexToBig k) = "Index to Big " ++ show k

export
Show Whole where
  show (W n prf) = show n

export
Show GateKind where
  show AND  = "AND"
  show XOR  = "XOR"
  show IOR  = "IOR"
  show NAND = "NAND"
  show XNOR = "XNOR"
  show NIOR = "NIOR"

export
Show BoolBinOp where
  show AND = "and"
  show IOR = "ior"
  show XOR = "xor"

export
Show ArithOp where
  show MUL = "mul"
  show DIV = "div"
  show ADD = "add"
  show SUB = "sub"

export
Show CompOp where
  show EQ = "eq"
  show LT = "lt"
  show GT = "gt"

export
Show Arithmetic.Expr where
  show (NatV x k) = show k
  show (R x) = (show . get) x
  show (Op x kind l r)
    = unwords ["(" <+> show kind, show l , show r <+> ")"]

export
Show Boolean.Expr where
  show (NatV x y) = show y
  show (BoolV x y) = show y
  show (R x) = (show . get) x
  show (Not x y) = unwords ["(not", show y <+> ")"]
  show (NatCmp x kind l r)
    = unwords ["(" <+> show kind, show l , show r <+> ")"]

  show (BoolCmp x kind l r)
    = unwords ["(" <+> show kind, show l , show r <+> ")"]

export
Show Flow.Error where
 show (CannotFlow x y)
   = "Cannot flow between: " ++ show x ++ " & " ++ show y


-- [ EOF ]
