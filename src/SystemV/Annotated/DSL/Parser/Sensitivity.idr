module SystemV.Annotated.DSL.Parser.Sensitivity

import Text.Lexer
import Text.Parser

import Toolkit.Text.Parser.Support

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Annotated.Types.Sensitivity

%default total

export
sensitivity : Rule Token Sensitivity
sensitivity
    =  gives "high"        High
   <|> gives "low"         Low
   <|> gives "rising"      Rising
   <|> gives "falling"     Falling
   <|> gives "insensitive" Insensitive

-- [ EOF ]
