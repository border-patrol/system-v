module SystemV.Common.Parser.Boolean

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location

import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Common.Types.Boolean
import SystemV.Common.Types.Nat.Comparison
import SystemV.Common.Types.Nat.Arithmetic

import SystemV.Common.Parser.Arithmetic as A

%default total

namespace Raw
  export
  true : Rule Bool
  true = gives "true" True

  export
  false : Rule Bool
  false = gives "false" False

  export
  value : Rule Bool
  value = true <|> false


boolOpKind : Rule BoolBinOp
boolOpKind
    = gives "and" AND
  <|> gives "ior" IOR
  <|> gives "xor" XOR

natOpKind : Rule CompOp
natOpKind
      = gives "lt" LT
    <|> gives "gt" GT
    <|> gives "eq" EQ

public export
data Expr : Type where
  NatV : FileContext -> A.Expr -> Expr
  BoolV : FileContext -> Bool -> Expr
  R : Ref -> Expr

  Not : FileContext -> Boolean.Expr -> Expr
  NatCmp : FileContext
        -> (kind : CompOp)
        -> (l,r  : Boolean.Expr)
                -> Expr

  BoolCmp : FileContext
         -> (kind : BoolBinOp)
         -> (l,r  : Boolean.Expr)
                 -> Expr

export
expr : Rule Boolean.Expr
expr =  WithFileContext.inserts A.expr NatV
    <|> WithFileContext.inserts value BoolV
    <|> inserts rawRef R
    <|> do s <- Toolkit.location
           symbol "("
           keyword "not"
           e <- Boolean.expr
           symbol ")"
           f <- Toolkit.location
           pure (Not (newFC s f) e)
    <|> do s <- Toolkit.location
           symbol "("
           k <- natOpKind
           l <- Boolean.expr
           r <- Boolean.expr
           symbol ")"
           e <- Toolkit.location
           pure (NatCmp (newFC s e) k l r)
    <|> do s <- Toolkit.location
           symbol "("
           k <- boolOpKind
           l <- Boolean.expr
           r <- Boolean.expr
           symbol ")"
           e <- Toolkit.location
           pure (BoolCmp (newFC s e) k l r)

-- [ EOF ]
