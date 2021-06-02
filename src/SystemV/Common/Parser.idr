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

export
sexpr : String
     -> Rule Token a
     -> (a -> b)
     -> Rule Token b
sexpr s value ctor
  = parens (inserts (keyword s *> value) ctor)


export
sexpr2 : String
      -> Rule Token a
      -> Rule Token b
      -> (a -> b -> c)
      -> Rule Token c
sexpr2 s pa pb ctor
    = sexpr s body build
  where
    body : Rule Token (a,b)
    body = (do {v <- pa; w <- pb; pure (v,w)})

    build : (a,b) -> c
    build (a,b) = ctor a b


export
sexpr3 : String
      -> Rule Token a
      -> Rule Token b
      -> Rule Token c
      -> (a -> b -> c -> d)
      -> Rule Token d
sexpr3 s pa pb pc ctor
    = sexpr s body build
  where
    body : Rule Token (a,b,c)
    body = (do {v <- pa; w <- pb; x <- pc; pure (v,w,x)})

    build : (a,b,c) -> d
    build (a,b,c) = ctor a b c

namespace WithFileContext
  export
  inserts : Rule Token a -> (FileContext -> a -> b) -> Rule Token b
  inserts value ctor
    = do s <- location
         v <- value
         e <- location
         pure (ctor (newFC s e) v)

  export
  inserts2 : Rule Token a
          -> Rule Token b
          -> (FileContext -> a -> b -> c)
          -> Rule Token c
  inserts2 pa pb ctor
      = inserts body build
    where
      body : Rule Token (a,b)
      body = (do {z <- pa; y <- pb; pure (z,y)})

      build : FileContext -> (a,b) -> c
      build fc (a,b) = ctor fc a b

  export
  gives : String -> (FileContext -> a) -> Rule Token a
  gives s ctor
    = do b <- location
         keyword s
         e <- location
         pure (ctor (newFC b e))

  export
  sexpr : String
       -> Rule Token a
       -> (FileContext -> a -> b)
       -> Rule Token b
  sexpr s value ctor = parens (inserts (keyword s *> value) ctor)


  export
  sexpr2 : String
        -> Rule Token a
        -> Rule Token b
        -> (FileContext -> a -> b -> c)
        -> Rule Token c
  sexpr2 s pa pb ctor
      = sexpr s body build
    where
      body : Rule Token (a,b)
      body = (do {v <- pa; w <- pb; pure (v,w)})

      build : FileContext -> (a,b) -> c
      build fc (a,b) = ctor fc a b

  export
  sexpr3 : String
        -> Rule Token a
        -> Rule Token b
        -> Rule Token c
        -> (FileContext -> a -> b -> c -> d)
        -> Rule Token d
  sexpr3 s pa pb pc ctor
      = sexpr s body build
    where
      body : Rule Token (a,b,c)
      body = (do {v <- pa; w <- pb; x <- pc; pure (v,w,x)})

      build : FileContext -> (a,b,c) -> d
      build fc (a,b,c) = ctor fc a b c
-- [ EOF ]
