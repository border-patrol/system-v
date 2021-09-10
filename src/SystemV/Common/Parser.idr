module SystemV.Common.Parser

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.String
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

namespace SystemV
  public export
  Rule : Type -> Type
  Rule = Rule () Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty () Token

  export
  eoi : RuleEmpty ()
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False

export
symbol : String -> Rule ()
symbol str
  = terminal ("Expected Symbol '" ++ str ++ "'")
             (\x => case x of
                           Symbol s => if s == str then Just ()
                                                   else Nothing
                           _ => Nothing)


export
keyword : String -> Rule ()
keyword str
  = terminal ("Expected Keyword '" ++ str ++ "'")
               (\x => case x of
                           Keyword s => if s == str then Just ()
                                                    else Nothing
                           _ => Nothing)

export
natLit : Rule Nat
natLit = terminal "Expected nat literal"
             (\x => case x of
                         LitNat i => Just i
                         _ => Nothing)

export
identifier : Rule String
identifier
  = terminal "Expected Identifier"
             (\x => case x of
                                ID str => Just str
                                _ => Nothing)

export
name : Rule String
name = identifier

export
braces : Inf (Rule a)
      -> Rule a
braces p = between (symbol "[")
                   (symbol "]") p

export
brackets : Inf (Rule a )
        -> Rule a
brackets p = between (symbol "{") (symbol "}") p

export
parens : Inf (Rule a)
      -> Rule a
parens p = between (symbol "(") (symbol ")") p

export
commaSepBy1 : Rule a -> Rule (List1 a)
commaSepBy1 = sepBy1 (symbol ",")

export
rawRef : Rule Ref
rawRef =
  do s <- Toolkit.location
     n <- name
     e <- Toolkit.location
     pure (MkRef (newFC s e) n)

export
gives : String -> a -> Rule a
gives s ctor
  = do keyword s
       pure ctor


export
inserts : Rule a -> (a -> b) -> Rule b
inserts value ctor
  = do v <- value
       pure (ctor v)

export
sexpr : String
     -> Rule a
     -> (a -> b)
     -> Rule b
sexpr s value ctor
  = parens (inserts (keyword s *> value) ctor)


export
sexpr2 : String
      -> Rule a
      -> Rule b
      -> (a -> b -> c)
      -> Rule c
sexpr2 s pa pb ctor
    = sexpr s body build
  where
    body : Rule (a,b)
    body = (do {v <- pa; w <- pb; pure (v,w)})

    build : (a,b) -> c
    build (a,b) = ctor a b


export
sexpr3 : String
      -> Rule a
      -> Rule b
      -> Rule c
      -> (a -> b -> c -> d)
      -> Rule d
sexpr3 s pa pb pc ctor
    = sexpr s body build
  where
    body : Rule (a,b,c)
    body = (do {v <- pa; w <- pb; x <- pc; pure (v,w,x)})

    build : (a,b,c) -> d
    build (a,b,c) = ctor a b c

namespace WithFileContext
  export
  inserts : Rule a -> (FileContext -> a -> b) -> Rule b
  inserts value ctor
    = do s <- Toolkit.location
         v <- value
         e <- Toolkit.location
         pure (ctor (newFC s e) v)

  export
  inserts2 : Rule a
          -> Rule b
          -> (FileContext -> a -> b -> c)
          -> Rule c
  inserts2 pa pb ctor
      = inserts body build
    where
      body : Rule (a,b)
      body = (do {z <- pa; y <- pb; pure (z,y)})

      build : FileContext -> (a,b) -> c
      build fc (a,b) = ctor fc a b

  export
  gives : String -> (FileContext -> a) -> Rule a
  gives s ctor
    = do b <- Toolkit.location
         keyword s
         e <- Toolkit.location
         pure (ctor (newFC b e))

  export
  sexpr : String
       -> Rule a
       -> (FileContext -> a -> b)
       -> Rule b
  sexpr s value ctor
    = do symbol "("
         res <- inserts (keyword s *> value) ctor
         symbol ")"
         pure res


  export
  sexpr2 : String
        -> Rule a
        -> Rule b
        -> (FileContext -> a -> b -> c)
        -> Rule c
  sexpr2 s pa pb ctor
      = sexpr s body build
    where
      body : Rule (a,b)
      body = (do {v <- pa; w <- pb; pure (v,w)})

      build : FileContext -> (a,b) -> c
      build fc (a,b) = ctor fc a b

  export
  sexpr3 : String
        -> Rule a
        -> Rule b
        -> Rule c
        -> (FileContext -> a -> b -> c -> d)
        -> Rule d
  sexpr3 s pa pb pc ctor
      = sexpr s body build
    where
      body : Rule (a,b,c)
      body = (do {v <- pa; w <- pb; x <- pc; pure (v,w,x)})

      build : FileContext -> (a,b,c) -> d
      build fc (a,b,c) = ctor fc a b c
-- [ EOF ]
