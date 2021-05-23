module SystemV.Common.Parser.Arithmetic

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location

import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location

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
  NatV : FileContext -> Nat -> Expr
  R    : Ref -> Expr
  Op   : FileContext
      -> (kind : ArithOp)
      -> (l,r  : Expr)
              -> Expr

export
value : Rule Token Expr
value = WithFileContext.inserts natLit NatV

export
expr : Rule Token Expr
expr =  value
    <|> inserts rawRef R
    <|> do s <- location
           symbol "("
           k <- arithOpKind
           l <- expr
           r <- expr
           symbol ")"
           e <- location
           pure (Op (newFC s e) k l r)

-- [ EOF ]
