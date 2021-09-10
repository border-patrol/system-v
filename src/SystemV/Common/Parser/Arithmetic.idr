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

arithOpKind : Rule ArithOp
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
value : Rule Expr
value = WithFileContext.inserts natLit NatV

export
expr : Rule Expr
expr =  value
    <|> inserts rawRef R
    <|> do s <- Toolkit.location
           symbol "("
           k <- arithOpKind
           l <- expr
           r <- expr
           symbol ")"
           e <- Toolkit.location
           pure (Op (newFC s e) k l r)

-- [ EOF ]
