module SystemV.Common.Lexer

import Text.Lexer

import Toolkit.Text.Lexer.Run

%default total


symbols : List String
symbols = ["-", "[", "]", ";", "{", "}", ",", "=", "(", ")", ".", "#", "!", "&", "|", "+"
          ]

keywords : List String
keywords = [ "input", "output", "inout"
           , "typedef"
           , "module", "endmodule"
           , "if", "begin", "else", "end"
           , "wire", "parameter"
           , "assign", "drive", "catch", "writeTo", "readFrom", "slice"
           , "logic"
           , "Top"
           , "not"
           , "and",  "ior", "xor"
           , "nand", "nior", "nxor"
           , "index"

           -- annotated
           , "high", "low", "rising", "falling", "insensitive"
           , "data", "address", "clock", "reset", "info", "interrupt", "control", "general"

           -- params
           , "eq", "lt", "gt"
           , "add", "mul", "sub", "div"
           , "nat", "datatype"
           , "for"
           ]

public export
data Identifier = MkIdentifier String

export
Eq Identifier where
  (==) (MkIdentifier x) (MkIdentifier y) = x == y

namespace SystemV
  public export
  data Token = ID String
               | Keyword String
               | LineComment String
               | BlockComment String
               | Documentation String
               | LitNat Nat
               | Symbol String
               | WS String
               | NotRecognised String
               | EndInput

  export
  Eq Token where
    (==) (ID x) (ID y) = x == y
    (==) (LineComment x) (LineComment y) = x == y
    (==) (BlockComment x) (BlockComment y) = x == y
    (==) (Keyword x) (Keyword y) = x == y
    (==) (LitNat x) (LitNat y) = x == y
    (==) (Symbol x) (Symbol y) = x == y
    (==) (WS x) (WS y) = x == y
    (==) (NotRecognised x) (NotRecognised y) = x == y
    (==) EndInput EndInput = True
    (==) _ _ = False


  identifier : Lexer
  identifier = pred startIdent <+> many (pred validIdent)
    where
      startIdent : Char -> Bool
      startIdent '_' = True
      startIdent x = isAlpha x

      validIdent : Char -> Bool
      validIdent '_' = True
      validIdent x = isAlphaNum x



  export
  tokenMap : TokenMap SystemV.Token
  tokenMap = with List
    [
      (space, WS)
    , (lineComment (exact "//"), LineComment)
    , (blockComment (exact "/*") (exact "*/"), BlockComment)
    , (digits, \x => LitNat (integerToNat $ cast {to=Integer} x))
    ]
    ++
       map (\x => (exact x, Symbol)) symbols
    ++
    [
      (identifier, (\x => if elem x keywords then Keyword x else ID x))
    , (any, NotRecognised)
    ]

keep : TokenData SystemV.Token -> Bool
keep t = case tok t of
    BlockComment _ => False
    LineComment  _ => False
    WS           _ => False
    _              => True

export
SystemVLexer : Lexer Token
SystemVLexer = MkLexer SystemV.tokenMap (keep) EndInput

export
lexSystemVStr : String -> Either LexError (List (TokenData Token))
lexSystemVStr = lexString SystemVLexer

export
lexSystemVFile : String -> IO $ Either LexFail (List (TokenData Token))
lexSystemVFile = lexFile SystemVLexer
