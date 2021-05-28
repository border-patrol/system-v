module SystemV.Core.DSL.Parser

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

import        SystemV.Core.DSL.AST

%default total

ref : Rule Token AST
ref = inserts rawRef Ref

logic : Rule Token AST
logic = WithFileContext.gives "logic" TyLogic

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


ports : Rule Token (List (String, AST))
ports
      =  symbol "(" *> symbol ")" *> pure Nil
     <|> do {p <- parens (commaSepBy1 port); pure (forget p)}
  where
    port : Rule Token (String, AST)
    port
      = do st <- location
           d <- direction
           keyword "wire"
           t <- type_
           label <- name
           e <- location
           pure (label, TyPort (newFC st e) t d)


writeTo : Rule Token AST
writeTo = sexpr "writeTo" ref WriteTo

readFrom : Rule Token AST
readFrom = sexpr "readFrom" ref ReadFrom

portArg : Rule Token (FileContext, AST)
portArg =   ref'
        <|> writeTo'
        <|> readFrom'
        <|> cast
        <|> slice
        <|> index
  where
    ref' : Rule Token (FileContext, AST)
    ref'
      = do s <- location
           r <- ref
           e <- location
           pure (newFC s e, r)

    writeTo' : Rule Token (FileContext, AST)
    writeTo'
      = do s <- location
           w <- writeTo
           e <- location
           pure (newFC s e, w)

    readFrom' : Rule Token (FileContext, AST)
    readFrom'
      = do s <- location
           w <- readFrom
           e <- location
           pure (newFC s e, w)

    index : Rule Token (FileContext, AST)
    index
      = do s <- location
           symbol "("
           keyword "index"
           n <- natLit
           p <- portArg
           symbol ")"
           e <- location
           pure (newFC s e, Index (newFC s e) n (snd p))

    slice : Rule Token (FileContext, AST)
    slice
      = do s <- location
           symbol "("
           keyword "slice"
           p <- portArg
           a <- natLit
           o <- natLit
           symbol ")"
           e <- location
           pure (newFC s e, Slice (newFC s e) (snd p) a o)

    cast : Rule Token (FileContext, AST)
    cast
      = do s <- location
           symbol "("
           keyword "cast"
           p <- portArg
           t <- type_
           d <- direction
           symbol ")"
           e <- location
           pure (newFC s e, Cast (newFC s e) (snd p) t d)

{- Does not pass the totality checker
portArg : Rule Token AST
portArg =  ref
       <|> sexpr "writeTo" ref WriteTo
       <|> writeTo
       <|> sexpr3 "slice" portArg natLit natLit Slice
       <|> sexpr3 "cast" portArg type_ direction Cast
       <|> sexpr2 "index" natLit portArg Index
-}

driveCatch : Rule Token AST
driveCatch = inserts (keyword "drive" *> writeTo)  Drive
         <|> inserts (keyword "catch" *> readFrom) Catch

assign : Rule Token AST
assign
  = do st <- location
       keyword "assign"
       commit
       r <- portArg
       symbol "="
       l <- portArg
       e <- location
       pure (Connect (newFC st e) (snd r) (snd l))

gateNot : Rule Token AST
gateNot = do s <- location
             keyword "not"
             symbol "("
             commit
             o <- portArg
             symbol ","
             i <- portArg
             symbol ")"
             e <- location
             pure (NotGate (newFC s e) (snd o) (snd i))

gate : Rule Token AST
gate
  = do s <- location
       ki <- gateKind
       symbol "("
       commit
       o <- portArg
       symbol ","
       ia <- portArg
       symbol ","
       ib <- portArg
       symbol ")"
       e <- location
       pure (Gate (newFC s e) ki (snd o) (snd ia) (snd ib))

gates : Rule Token AST
gates = gateNot <|> gate

expr : Rule Token AST
expr = driveCatch <|> assign <|> gates

endModule : Rule Token AST
endModule
   = do s <- location
        keyword "endmodule"
        e <- location
        pure (EndModule (newFC s e))

moduleInst : Rule Token (FileContext, String, AST)
moduleInst
    = do s <- location
         f <- ref
         n <- name
         as <- parens (commaSepBy1 portArg)
         e <- location
         pure ((newFC s e), n, mkApp f as)
  where
    mkApp : AST
         -> List1 (FileContext, AST)
         -> AST
    mkApp f ((fc, a):::as)
      = foldl (\acc, (fc,a) => App fc acc a) (App fc f a) as

mutual
  cond : Rule Token AST
  cond
    = do s <- location
         keyword "if"
         commit
         c <- portArg
         keyword "begin"
         t <- entries False
         keyword "end"
         keyword "else"
         keyword "begin"
         f <- entries False
         keyword "end"
         e <- location
         pure (IfThenElse (newFC s e) (snd c) t f)

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


  collapse : AST -> List1 MBody -> AST
  collapse l (x:::xs)
      = foldr foldEntry l (x::xs)
    where
      foldEntry : MBody -> AST -> AST
      foldEntry (Expr expr) body
        = Seq (getFC expr) expr body
      foldEntry (Bindable (fc, n, e)) body
        = Let fc n e body
      foldEntry (TDef (fc, n, e)) body
        = Let fc n e body

  entries : Bool -> Rule Token AST
  entries True
      = do es <- some entry
           m <- endModule
           pure (collapse m es)
  entries False
      = do es <- some entry
           l <- location
           pure (collapse (UnitVal (newFC l l)) es)


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
               -> FileContext
               -> AST
               -> List (String, AST)
               -> AST
      buildFunc ty fc k Nil
        = Func fc "()" (TyUnit ty) k

      buildFunc _ fc b ports
        = foldPorts fc b ports

      moduleFunc : Rule Token AST
      moduleFunc = do s <- location
                      xs <- ports
                      e1 <- location
                      symbol ";"
                      es <- (entries True <|> endModule)
                      e <- location
                      pure (buildFunc (newFC s e1) (newFC s e) es xs)

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

namespace Core
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
