module SystemV.Common.Parser.Arithmetic

import Text.Lexer
import Text.Parser

import Toolkit.Text.Parser.Support

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Common.Types.Nat.Arithmetic

%default total

arithOpKind : Rule Token ArithOp
arithOpKind
    = gives "mul" MUL
  <|> gives "div" DIV
  <|> gives "add" ADD
  <|> gives "sub" SUB


public export
data Expr : Type where
  NatV : Nat -> Expr
  R    : Ref -> Expr
  Op   : (kind : ArithOp)
      -> (l,r  : Expr)
              -> Expr

export
expr : Rule Token Expr
expr =  inserts natLit NatV
    <|> inserts rawRef R
    <|> do symbol "("
           k <- arithOpKind
           l <- expr
           r <- expr
           symbol ")"
           pure (Op k l r)

-- [ EOF ]
