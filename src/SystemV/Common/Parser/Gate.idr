module SystemV.Common.Parser.Gate

import Text.Lexer
import Text.Parser

import Toolkit.Text.Parser.Support

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Common.Types.Gate

%default total

export
gateKind : Rule Token GateKind
gateKind
    = gives "and"    AND
  <|> gives "xor"    XOR
  <|> gives "ior"    IOR
  <|> gives "nand"   NAND
  <|> gives "xnor"   XNOR
  <|> gives "nior"   NIOR


-- [ EOF ]
