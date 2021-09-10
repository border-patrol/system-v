module SystemV.Common.Parser.Direction

import Text.Lexer
import Text.Parser

import Toolkit.Text.Parser.Support

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Common.Types.Direction

%default total

export
direction : Rule Direction
direction = gives "input"  IN
        <|> gives "output" OUT
        <|> gives "inout"  INOUT


-- [ EOF ]
