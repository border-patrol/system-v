module SystemV.Annotated.DSL.Parser.Intention

import Text.Lexer
import Text.Parser

import Toolkit.Text.Parser.Support

import SystemV.Common.Lexer
import SystemV.Common.Parser

import SystemV.Annotated.Types.Intention

%default total

export
intention : Rule Token Intention
intention
    =  gives "data"      Data
   <|> gives "address"   Address
   <|> gives "clock"     Clock
   <|> gives "reset"     Reset
   <|> gives "info"      Info
   <|> gives "interrupt" Interrupt
   <|> gives "control"   Control
   <|> gives "general"   General

-- [ EOF ]
