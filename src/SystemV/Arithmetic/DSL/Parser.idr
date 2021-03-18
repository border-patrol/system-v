module SystemV.Arithmetic.DSL.Parser

import        Data.Vect
import        Data.Nat
import        Data.List
import        Data.List.Views
import        Data.Strings
import        Data.Maybe

import public Text.Lexer
import public Text.Parser

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import        Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import        SystemV.Types.Direction
import        SystemV.Types.Gate

import        SystemV.Arithmetic.DSL.AST


import public SystemV.DSL.Lexer

%default total -- Idris2 does it!

eoi : RuleEmpty Token ()
eoi = eoi isEOI
  where
    isEOI : Token -> Bool
    isEOI EndInput = True
    isEOI _ = False

symbol : String -> Rule Token ()
symbol str
  = terminal ("Expected Symbol '" ++ str ++ "'")
             (\x => case tok x of
                           Symbol s => if s == str then Just ()
                                                   else Nothing
                           _ => Nothing)


keyword : String -> Rule Token ()
keyword str
  = terminal ("Expected Keyword '" ++ str ++ "'")
               (\x => case tok x of
                           Keyword s => if s == str then Just ()
                                                    else Nothing
                           _ => Nothing)


natLit : Rule Token Nat
natLit = terminal "Expected nat literal"
             (\x => case tok x of
                         LitNat i => Just i
                         _ => Nothing)

identifier : Rule Token String
identifier
  = terminal "Expected Identifier"
             (\x => case tok x of
                                ID str => Just str
                                _ => Nothing)

name : Rule Token String
name = identifier

braces : Inf (Rule Token a)
      -> Rule Token a
braces = between (symbol "[")
                 (symbol "]")

brackets : Inf (Rule Token a )
        -> Rule Token a
brackets = between (symbol "{") (symbol "}")

parens : Inf (Rule Token a)
      -> Rule Token a
parens = between (symbol "(") (symbol ")")

semiSepBy1 : Rule Token a -> Rule Token (List a)
semiSepBy1 = sepBy1 (symbol ";")

commaSepBy1 : Rule Token a -> Rule Token (List a)
commaSepBy1 = sepBy1 (symbol ",")

commaSepBy1' : Rule Token a -> Rule Token (xs : List a ** NonEmpty xs)
commaSepBy1' = sepBy1' (symbol ",")


sepBy1V : (sep : Rule Token b)
       -> (p : Rule Token a)
       -> Rule Token (n ** Vect (S n) a)
sepBy1V sep p = do {x <- p; xs <- many (sep *> p); pure (_ ** fromList $ x::xs)}

sepBy2V : (sep : Rule Token b)
       -> (p : Rule Token a)
       -> Rule Token (n ** Vect (S (S n)) a)
sepBy2V sep p = do {x <- p; sep; y <- p; rest <- many (sep *> p); pure (_ ** fromList $ x::y::rest)}

commaSepBy1V : (p : Rule Token a) -> Rule Token (n ** Vect (S n) a)
commaSepBy1V = sepBy1V (symbol ",")

commaSepBy2V : (p : Rule Token a) -> Rule Token (n ** Vect (S (S n)) a)
commaSepBy2V = sepBy2V (symbol ",")

ref : Rule Token AST
ref = do
  s <- location
  n <- name
  e <- location
  pure (Ref (newFC s e) n)


logic : Rule Token AST
logic = do
  s <- location
  keyword "logic"
  e <- location
  pure (TyLogic (newFC s e))

array : Rule Token AST
array = do
  s <- location
  ty <- ref <|> logic
  symbol "["
  commit
  idx <- natLit
  symbol "]"
  e <- location
  pure (TyVect (newFC s e) idx ty)


type_ : Rule Token AST
type_ = array <|> logic <|> ref

slice : Rule Token AST
slice
  = do s <- location
       symbol "("
       keyword "slice"
       r <- ref
       alpha <- natLit
       omega <- natLit
       symbol ")"
       e <- location
       pure (Slice (newFC s e) r alpha omega)

chanDef : Rule Token (FileContext, String, AST)
chanDef
  = do st <- location
       keyword "wire"
       commit
       ty <- type_
       n <- name
       e <- location
       pure (newFC st e, n, MkChan (newFC st e) ty)

typeDef : Rule Token (FileContext, String, AST)
typeDef = do
  s <- location
  keyword "typedef"
  commit
  decl <- type_
  n <- name
  e <- location
  pure (newFC s e, n, decl)


direction : Rule Token Direction
direction = do {keyword "input"; pure IN}
        <|> do {keyword "output"; pure OUT}
        <|> do {keyword "inout";  pure INOUT}


paramDecl : Rule Token String
paramDecl
  = do st <- location
       keyword "parameter"
       label <- name
       e <- location
       pure (label)

paramDecls : Rule Token (List String)
paramDecls = symbol "#" *> parens (commaSepBy1 paramDecl)

port : Rule Token (String, AST)
port
  = do st <- location
       d <- direction
       keyword "wire"
       t <- type_
       label <- name
       e <- location
       pure (label, TyPort (newFC st e) t d)

ports : Rule Token (List (String, AST))
ports =  symbol "(" *> symbol ")" *> pure Nil
     <|> parens (commaSepBy1 port)

assign : Rule Token AST
assign
  = do st <- location
       keyword "assign"
       commit
       r <- ref
       symbol "="
       l <- (ref <|> slice)
       e <- location
       pure (Connect (newFC st e) r l)

cast : Rule Token AST
cast
  = do st <- location
       keyword "cast"
       p <- (ref <|> slice)
       t <- type_
       d <- direction
       e <- location
       pure (Cast (newFC st e) p t d)

param : Rule Token AST
param =   ref
      <|> do st <- location
             n <- natLit
             e <- location
             pure (MkParam (newFC st e) n)

params : Rule Token (as : List AST ** NonEmpty as)
params
  = do symbol "#"
       ps <- parens (commaSepBy1' param)
       pure ps

paramOp : String -> Rule Token (AST, AST)
paramOp s = parens body
  where
    body : Rule Token (AST, AST)
    body = do keyword s
              commit
              a <- param
              b <- param
              pure (a,b)

paramOpBool : String -> (Nat -> Nat -> Bool) -> Rule Token AST
paramOpBool s op
  = do st <- location
       lr <- paramOp s
       e <- location
       pure (ParamOpBool (newFC st e) op (fst lr) (snd lr))

paramOpArith : String -> (Nat -> Nat -> Nat) -> Rule Token AST
paramOpArith s op
  = do st <- location
       lr <- paramOp s
       e <- location
       pure (ParamOpArith (newFC st e) op (fst lr) (snd lr))

paramOpNot :  Rule Token AST
paramOpNot
    = do st <- location
         p <- parens (keyword "not" *> param)
         e <- location
         pure (ParamOpNot (newFC st e) p)

paramOpsB : Rule Token AST
paramOpsB =   paramOpBool "lt"  (<)
          <|> paramOpBool "gt"  (>)
          <|> paramOpBool "eq"  (==)
          <|> paramOpNot

paramOpsA : Rule Token AST
paramOpsA =  paramOpArith "add" (+)
         <|> paramOpArith "sub" (minus)
         <|> paramOpArith "mul" (*)

proj : Rule Token AST
    -> String
    -> (FileContext -> AST -> AST)
    -> Rule Token AST
proj p s ctor
  = do st <- location
       symbol "("
       keyword s
       commit
       n <- p
       symbol ")"
       e <- location
       pure (ctor (newFC st e) n)

writeTo : Rule Token AST
writeTo = (proj (ref <|> slice) "writeTo" WriteTo)

readFrom : Rule Token AST
readFrom = (proj (ref <|> slice) "readFrom" ReadFrom)


mutual
  cond : Rule Token AST
  cond
    = do s <- location
         keyword "if"
         commit
         c <- (paramOpsB <|> ref)
         keyword "begin"
         t <- entries False
         keyword "end"
         keyword "else"
         keyword "begin"
         f <- entries False
         keyword "end"
         e <- location
         pure (IfThenElse (newFC s e) c t f)


  projChan : Rule Token AST
  projChan = readFrom
         <|> writeTo

  driveCatch : Rule Token AST
  driveCatch = (proj (writeTo)  "drive"    Drive)
           <|> (proj (readFrom) "catch"    Catch)

  gateNot : Rule Token AST
  gateNot = do s <- location
               keyword "not"
               symbol "("
               commit
               o <- ref <|> slice <|> projChan
               symbol ","
               i <- ref <|> slice <|> projChan
               symbol ")"
               e <- location
               pure (NotGate (newFC s e) o i)

  gate : (kword : String)
      -> (kind  : GateKind)
               -> Rule Token AST
  gate k ki
    = do s <- location
         keyword k
         symbol "("
         commit
         o <- ref <|> slice <|> projChan
         symbol ","
         ia <- ref <|> slice <|> projChan
         symbol ","
         ib <- ref <|> slice <|> projChan
         symbol ")"
         e <- location
         pure (Gate (newFC s e) ki o ia ib)

  gates : Rule Token AST
  gates = gateNot
      <|> gate "nand" NAND
      <|> gate "and"  AND
      <|> gate "nor"  NIOR
      <|> gate "or"   IOR
      <|> gate "nxor" XNOR
      <|> gate "xor"  XOR

  expr : Rule Token AST
  expr = driveCatch <|> assign <|> gates

  moduleInst : Rule Token (FileContext, String, AST)
  moduleInst
      = do s <- location
           f <- ref
           ps <- optional params
           n <- name
           as <- parens (commaSepBy1' (ref <|> projChan <|> parens cast <|> slice))
           e <- location
           pure ((newFC s e), n, case ps of
                      Just ps' => mkApp f ps' as
                      Nothing  => mkApp' f as )
    where
      mkApp' : AST
           -> (as : List AST ** NonEmpty as)
           -> AST
      mkApp' f (a::as ** IsNonEmpty)
        = foldl App (App f a) as

      mkApp : AST
           -> (ps : List AST ** NonEmpty ps)
           -> (as : List AST ** NonEmpty as)
           -> AST
      mkApp f (p::ps ** IsNonEmpty) (a::as ** IsNonEmpty)
        = foldl App (App f p) (ps ++ (a::as))

  data MBody = Expr AST
             | TDef (FileContext, String, AST)
             | Bindable (FileContext, String, AST)

  export
  entry : Rule Token MBody
  entry = (entry' <* symbol ";")
      <|> (do {c <- cond; pure (Expr c)})
      <|> (do {m <- moduleDef; pure (Bindable m)})
    where
      entry' : Rule Token MBody
      entry' = (do { e <- expr;                     pure (Expr     e)})
           <|> (do { d <- typeDef;                  pure (TDef     d)})
           <|> (do { c <- (chanDef <|> moduleInst); pure (Bindable c)})

  entries : Bool -> Rule Token AST
  entries howEnd
      = do es <- some' entry
           pure (collapse howEnd es)
    where

      foldEntry : MBody -> AST -> AST
      foldEntry (Expr expr) body
        = Seq expr body
      foldEntry (Bindable (fc, n, e)) body
        = Let fc n e body
      foldEntry (TDef (fc, n, e)) body
        = TypeDef fc n e body

      lastTerm : Bool -> AST
      lastTerm True = EndModule
      lastTerm False = UnitVal

      collapse : Bool -> (es : List MBody ** NonEmpty es) -> AST
      collapse b (x::xs ** IsNonEmpty)
        = foldr foldEntry (lastTerm b) (x::xs)

  moduleDefGen : Rule Token String -> Rule Token (FileContext, String, AST)
  moduleDefGen p
      = do s <- location
           keyword "module"
           n <- p
           value <- moduleFunc
           e <- location
           pure (newFC s e, n, value)
    where
      foldPort : FileContext
               -> (String, AST)
               -> AST
               -> AST
      foldPort fc (n,ty) acc = Func fc n ty acc

      foldPorts : FileContext
               -> AST
               -> List (String, AST)
               -> AST
      foldPorts fc = foldr (foldPort fc)

      foldParam : FileContext
               -> String
               -> AST
               -> AST
      foldParam fc p acc = Func fc p TyParam acc

      foldParams : FileContext
                -> AST
                -> List String
                -> AST
      foldParams fc = foldr (foldParam fc)

      buildFunc : FileContext
               -> AST
               -> List String
               -> List (String, AST)
               -> AST
      buildFunc fc body Nil    Nil
        = Func fc "" TyUnit body
      buildFunc fc body params Nil
        = foldParams fc body params
      buildFunc fc body Nil ports
        = foldPorts fc body ports
      buildFunc fc body params ports
        = foldParams fc (foldPorts fc body ports) params

      moduleFunc : Rule Token AST
      moduleFunc = do s <- location
                      ps <- option Nil paramDecls
                      xs <- ports
                      symbol ";"
                      es <- option EndModule (entries True)
                      keyword "endmodule"
                      e <- location
                      pure (buildFunc (newFC s e) es ps xs)

  moduleDef : Rule Token (FileContext, String, AST)
  moduleDef = moduleDefGen name

data Decl = TDecl (FileContext, String, AST)
          | MDecl (FileContext, String, AST)

export
decls : RuleEmpty Token (List Decl)
decls = many (do {m <- moduleDef; pure (MDecl m)}
          <|> do {t <- typeDef <* symbol ";"; pure (TDecl t)})

export
top : Rule Token AST
top = pure $ (snd . snd) !(moduleDefGen isTop)
  where
    isTop : Rule Token String
    isTop = do keyword "Top"
               pure "Top"

export
design : Rule Token AST
design = do ds <- decls
            t <- top
            pure (foldDecls t ds)
  where
    foldDecl : Decl -> AST -> AST
    foldDecl (TDecl (fc, n, e)) body = TypeDef fc n e body
    foldDecl (MDecl (fc, n, e)) body = Let fc n e body

    foldDecls : AST
             -> List Decl
             -> AST
    foldDecls = foldr foldDecl

export
parseSystemVStr : {e   : _}
             -> (rule : Grammar (TokenData Token) e ty)
             -> (str : String)
             -> Either (Run.ParseError Token) ty
parseSystemVStr rule str
  = parseString SystemVLexer rule str

export
parseSystemVFile : {e     : _}
              -> (rule  : Grammar (TokenData Token) e ty)
              -> (fname : String)
                       -> IO (Either (Run.ParseError Token) ty)
parseSystemVFile
  = parseFile SystemVLexer

export
parseSystemVDesignFile : (fname : String)
                    -> IO (Either (Run.ParseError Token) AST)
parseSystemVDesignFile
  = parseFile SystemVLexer design

-- [ EOF ]
