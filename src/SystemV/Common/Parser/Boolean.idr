module SystemV.Common.Parser.Boolean

import Text.Lexer
import Text.Parser

import Toolkit.Text.Parser.Support

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Common.Types.Boolean
import SystemV.Common.Types.Nat.Comparison

%default total

namespace Raw
  export
  true : Rule Token Bool
  true = gives "true" True

  export
  false : Rule Token Bool
  false = gives "false" False

  export
  value : Rule Token Bool
  value = true <|> false


boolOpKind : Rule Token BoolBinOp
boolOpKind
    = gives "and" AND
  <|> gives "ior" IOR
  <|> gives "xor" XOR

natOpKind : Rule Token CompOp
natOpKind
      = gives "lt" LT
    <|> gives "gt" GT
    <|> gives "eq" EQ

public export
data Expr : Type where
  NatV : Nat -> Expr
  BoolV : Bool -> Expr
  R : Ref -> Expr

  Not : Expr -> Expr
  NatCmp : (kind : CompOp)
        -> (l,r  : Expr)
                -> Expr
  BoolCmp : (kind : BoolBinOp)
         -> (l,r  : Expr)
                 -> Expr

export
expr : Rule Token Expr
expr =  inserts natLit NatV
    <|> inserts value BoolV
    <|> inserts rawRef R
    <|> do symbol "("
           keyword "not"
           e <- expr
           symbol ")"
           pure (Not e)
    <|> do symbol "("
           k <- natOpKind
           l <- expr
           r <- expr
           symbol ")"
           pure (NatCmp k l r)
    <|> do symbol "("
           k <- boolOpKind
           l <- expr
           r <- expr
           symbol ")"
           pure (BoolCmp k l r)

-- [ EOF ]
