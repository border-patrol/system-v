module SystemV.Annotated.DSL.Parser

import        Data.Vect
import        Data.Nat
import        Data.List

import        Data.List.Views
import        Data.List1
import        Data.Strings
import        Data.Maybe

import public Text.Lexer
import public Text.Parser

import public Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import public Toolkit.Text.Parser.Support
import        Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import public SystemV.Common.Lexer
import        SystemV.Common.Parser

import        SystemV.Common.Parser.Direction
import        SystemV.Common.Parser.Gate

import        SystemV.Annotated.DSL.Parser.Intention
import        SystemV.Annotated.DSL.Parser.Sensitivity

import        SystemV.Annotated.DSL.AST

%default total

ref : Rule Token AST
ref = inserts rawRef Ref

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
writeTo = (proj ref "writeTo" WriteTo)

readFrom : Rule Token AST
readFrom = (proj ref "readFrom" ReadFrom)

projChan : Rule Token AST
projChan = readFrom
       <|> writeTo

drive : Rule Token AST
drive
  = do st <- location
       symbol "("
       keyword "drive"
       commit
       p <- writeTo
       s <- sensitivity
       i <- intention
       symbol ")"
       e <- location
       pure (Drive (newFC st e) s i p)


driveCatch : Rule Token AST
driveCatch = drive
         <|> (proj (readFrom) "catch"    Catch)

mutual
  index : Rule Token AST
  index
    = do s <- location
         symbol "("
         keyword "index"
         n <- natLit
         p <- (ref <|> projChan <|> slidx)
         symbol ")"
         e <- location
         pure (Index (newFC s e) n p)

  slice : Rule Token AST
  slice
    = do s <- location
         symbol "("
         keyword "slice"
         r <- (ref <|> projChan <|> slidx)
         alpha <- natLit
         omega <- natLit
         symbol ")"
         e <- location
         pure (Slice (newFC s e) r alpha omega)

  slidx : Rule Token AST
  slidx = slice <|> index


portP : Rule Token AST
portP = ref <|> slidx <|> projChan

chanDef : Rule Token (FileContext, String, AST)
chanDef
  = do st <- location
       i <- intention
       s <- sensitivity
       keyword "wire"
       commit
       ty <- type_
       n <- name
       e <- location
       pure (newFC st e, n, MkChan (newFC st e) ty s i)

typeDef : Rule Token (FileContext, String, AST)
typeDef = do
  s <- location
  keyword "typedef"
  commit
  decl <- type_
  n <- name
  e <- location
  pure (newFC s e, n, decl)

port : Rule Token (String, AST)
port
  = do st <- location
       i <- intention
       s <- sensitivity
       d <- direction
       keyword "wire"
       t <- type_
       label <- name
       e <- location
       pure (label, TyPort (newFC st e) t d s i)

ports : Rule Token (List (String, AST))
ports =  symbol "(" *> symbol ")" *> pure Nil
     <|> do {p <- parens (commaSepBy1 port); pure (forget p)}

assign : Rule Token AST
assign
  = do st <- location
       keyword "assign"
       commit
       r <- (ref <|> slidx)
       symbol "="
       l <- (ref <|> slidx)
       e <- location
       pure (Connect (newFC st e) r l)


cast : Rule Token AST
cast
  = do st <- location
       keyword "cast"
       p <- (ref <|> slidx)
       t <- type_
       d <- direction
       s <- sensitivity
       i <- intention
       e <- location
       pure (Cast (newFC st e) p t d s i)

mutual
  cond : Rule Token AST
  cond
    = do s <- location
         keyword "if"
         commit
         c <- ref
         keyword "begin"
         t <- entries False
         keyword "end"
         keyword "else"
         keyword "begin"
         f <- entries False
         keyword "end"
         e <- location
         pure (IfThenElse (newFC s e) c t f)

  gateNot : Rule Token AST
  gateNot = do s <- location
               keyword "not"
               symbol "("
               commit
               o <- portP
               symbol ","
               i <- portP
               symbol ")"
               e <- location
               pure (NotGate (newFC s e) o i)

  gate : Rule Token AST
  gate
    = do s <- location
         ki <- gateKind
         symbol "("
         commit
         o <- portP
         symbol ","
         ia <- portP
         symbol ","
         ib <- portP
         symbol ")"
         e <- location
         pure (Gate (newFC s e) ki o ia ib)

  gates : Rule Token AST
  gates = gateNot <|> gate

  expr : Rule Token AST
  expr = driveCatch <|> assign <|> gates

  appArg : Rule Token AST
  appArg = ref <|> projChan <|> parens cast <|> slidx

  moduleInst : Rule Token (FileContext, String, AST)
  moduleInst
      = do s <- location
           f <- ref
           n <- name
           as <- parens (commaSepBy1 appArg)
           e <- location
           pure ((newFC s e), n, mkApp f as)
    where
      mkApp : AST
           -> List1 AST
           -> AST
      mkApp f (a:::as)
        = foldl App (App f a) as

  data MBody = Expr AST
             | TDef (FileContext, String, AST)
             | Bindable (FileContext, String, AST)


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
        = Let fc n e body

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

      buildFunc : FileContext
               -> AST
               -> List (String, AST)
               -> AST
      buildFunc fc body Nil
        = Func fc "" TyUnit body
      buildFunc fc body ports
        = foldPorts fc body ports

      moduleFunc : Rule Token AST
      moduleFunc = do s <- location
                      xs <- ports
                      symbol ";"
                      es <- option EndModule (entries True)
                      keyword "endmodule"
                      e <- location
                      pure (buildFunc (newFC s e) es xs)

  moduleDef : Rule Token (FileContext, String, AST)
  moduleDef = moduleDefGen name

data Decl = TDecl (FileContext, String, AST)
          | MDecl (FileContext, String, AST)

decls : RuleEmpty Token (List Decl)
decls = many (do {m <- moduleDef; pure (MDecl m)}
          <|> do {t <- typeDef <* symbol ";"; pure (TDecl t)})

top : Rule Token AST
top = pure $ (snd . snd) !(moduleDefGen isTop)
  where
    isTop : Rule Token String
    isTop = do keyword "Top"
               pure "Top"

design : Rule Token AST
design = do ds <- decls
            t <- top
            pure (foldDecls t ds)
  where
    foldDecl : Decl -> AST -> AST
    foldDecl (TDecl (fc, n, e)) body = Let fc n e body
    foldDecl (MDecl (fc, n, e)) body = Let fc n e body

    foldDecls : AST
             -> List Decl
             -> AST
    foldDecls = foldr foldDecl

namespace Annotated

  parseSystemVStr : {e   : _}
               -> (rule : Grammar (TokenData Token) e ty)
               -> (str : String)
               -> Either (Run.ParseError Token) ty
  parseSystemVStr rule str
    = parseString SystemVLexer rule str

  parseSystemVFile : {e     : _}
                -> (rule  : Grammar (TokenData Token) e ty)
                -> (fname : String)
                         -> IO (Either (Run.ParseError Token) ty)
  parseSystemVFile
    = parseFile SystemVLexer

  export
  fromFile : (fname : String)
                   -> IO (Either (Run.ParseError Token) AST)
  fromFile fname
    = case !(parseFile SystemVLexer design fname) of
        Left err  => pure (Left err)
        Right ast => pure (Right (setFileName fname ast))

-- [ EOF ]
