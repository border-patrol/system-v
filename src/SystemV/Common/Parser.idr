module SystemV.Common.Parser

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.Strings
import Data.Maybe

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location
import Toolkit.Text.Parser.Run

import SystemV.Common.Lexer

import public SystemV.Common.Parser.Ref

import SystemV.Core.DSL.AST

%default total

export
eoi : RuleEmpty Token ()
eoi = eoi isEOI
  where
    isEOI : Token -> Bool
    isEOI EndInput = True
    isEOI _ = False

export
symbol : String -> Rule Token ()
symbol str
  = terminal ("Expected Symbol '" ++ str ++ "'")
             (\x => case tok x of
                           Symbol s => if s == str then Just ()
                                                   else Nothing
                           _ => Nothing)


export
keyword : String -> Rule Token ()
keyword str
  = terminal ("Expected Keyword '" ++ str ++ "'")
               (\x => case tok x of
                           Keyword s => if s == str then Just ()
                                                    else Nothing
                           _ => Nothing)

export
natLit : Rule Token Nat
natLit = terminal "Expected nat literal"
             (\x => case tok x of
                         LitNat i => Just i
                         _ => Nothing)

export
identifier : Rule Token String
identifier
  = terminal "Expected Identifier"
             (\x => case tok x of
                                ID str => Just str
                                _ => Nothing)

export
name : Rule Token String
name = identifier

export
braces : Inf (Rule Token a)
      -> Rule Token a
braces = between (symbol "[")
                 (symbol "]")

export
brackets : Inf (Rule Token a )
        -> Rule Token a
brackets = between (symbol "{") (symbol "}")

export
parens : Inf (Rule Token a)
      -> Rule Token a
parens = between (symbol "(") (symbol ")")

export
commaSepBy1 : Rule Token a -> Rule Token (List1 a)
commaSepBy1 = sepBy1 (symbol ",")

export
sexpr : Rule Token a
     -> Rule Token b
     -> Rule Token (a,b)
sexpr pHead pBody
  = parens $ do h <- pHead
                b <- pBody
                pure (h,b)

export
rawRef : Rule Token Ref
rawRef =
  do s <- location
     n <- name
     e <- location
     pure (MkRef (newFC s e) n)

export
gives : String -> a -> Rule Token a
gives s ctor
  = do keyword s
       pure ctor

export
inserts : Rule Token a -> (a -> b) -> Rule Token b
inserts value ctor
  = do v <- value
       pure (ctor v)

-- [ EOF ]
