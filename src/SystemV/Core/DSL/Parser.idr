module SystemV.Core.DSL.Parser

import        Data.Vect
import        Data.Nat
import        Data.List

import        Data.List.Views
import        Data.List1
import        Data.String
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

ref : Rule AST
ref = inserts rawRef Ref

logic : Rule AST
logic = WithFileContext.gives "logic" TyLogic

array : Rule AST
array = do
  s <- Toolkit.location
  ty <- ref <|> logic
  symbol "["
  commit
  idx <- natLit
  symbol "]"
  e <- Toolkit.location
  pure (TyVect (newFC s e) idx ty)


type_ : Rule AST
type_ = array <|> logic <|> ref

chanDef : Rule (FileContext, String, AST)
chanDef
  = do st <- Toolkit.location
       keyword "wire"
       commit
       ty <- type_
       n <- name
       e <- Toolkit.location
       pure (newFC st e, n, MkChan (newFC st e) ty)

typeDef : Rule (FileContext, String, AST)
typeDef = do
  s <- Toolkit.location
  keyword "typedef"
  commit
  decl <- type_
  n <- name
  e <- Toolkit.location
  pure (newFC s e, n, decl)


ports : Rule (List (String, AST))
ports
      =  symbol "(" *> symbol ")" *> pure Nil
     <|> do {p <- parens (commaSepBy1 port); pure (forget p)}
  where
    port : Rule (String, AST)
    port
      = do st <- Toolkit.location
           d <- direction
           keyword "wire"
           t <- type_
           label <- name
           e <- Toolkit.location
           pure (label, TyPort (newFC st e) t d)


portArg : Rule (FileContext, AST)
portArg =   (do r <- ref; pure (getFC r, r))
        <|> writeTo
        <|> readFrom
        <|> cast
        <|> slice
        <|> index
  where
    writeTo : Rule (FileContext, AST)
    writeTo
      = do s <- Toolkit.location
           symbol "("
           keyword "writeTo"
           p <- portArg
           symbol ")"
           e <- Toolkit.location
           pure (newFC s e, WriteTo (newFC s e) (snd p))

    readFrom : Rule (FileContext, AST)
    readFrom
      = do s <- Toolkit.location
           symbol "("
           keyword "readFrom"
           p <- portArg
           symbol ")"
           e <- Toolkit.location
           pure (newFC s e, ReadFrom (newFC s e) (snd p))

    index : Rule (FileContext, AST)
    index
      = do s <- Toolkit.location
           symbol "("
           keyword "index"
           n <- natLit
           p <- portArg
           symbol ")"
           e <- Toolkit.location
           pure (newFC s e, Index (newFC s e) n (snd p))

    slice : Rule (FileContext, AST)
    slice
      = do s <- Toolkit.location
           symbol "("
           keyword "slice"
           p <- portArg
           a <- natLit
           o <- natLit
           symbol ")"
           e <- Toolkit.location
           pure (newFC s e, Slice (newFC s e) (snd p) a o)

    cast : Rule (FileContext, AST)
    cast
      = do s <- Toolkit.location
           symbol "("
           keyword "cast"
           p <- portArg
           t <- type_
           d <- direction
           symbol ")"
           e <- Toolkit.location
           pure (newFC s e, Cast (newFC s e) (snd p) t d)

driveCatch : Rule AST
driveCatch = inserts (do p <- (keyword "drive" *> portArg); pure (snd p))  Drive
         <|> inserts (do p <- (keyword "catch" *> portArg); pure (snd p)) Catch

assign : Rule AST
assign
  = do st <- Toolkit.location
       keyword "assign"
       commit
       r <- portArg
       symbol "="
       l <- portArg
       e <- Toolkit.location
       pure (Connect (newFC st e) (snd r) (snd l))

gateNot : Rule AST
gateNot = do s <- Toolkit.location
             keyword "not"
             symbol "("
             commit
             o <- portArg
             symbol ","
             i <- portArg
             symbol ")"
             e <- Toolkit.location
             pure (NotGate (newFC s e) (snd o) (snd i))

gate : Rule AST
gate
  = do s <- Toolkit.location
       ki <- gateKind
       symbol "("
       commit
       o <- portArg
       symbol ","
       ia <- portArg
       symbol ","
       ib <- portArg
       symbol ")"
       e <- Toolkit.location
       pure (Gate (newFC s e) ki (snd o) (snd ia) (snd ib))

gates : Rule AST
gates = gateNot <|> gate

expr : Rule AST
expr = driveCatch <|> assign <|> gates

endModule : Rule AST
endModule
   = do s <- Toolkit.location
        keyword "endmodule"
        e <- Toolkit.location
        pure (EndModule (newFC s e))

moduleInst : Rule (FileContext, String, AST)
moduleInst
    = do s <- Toolkit.location
         f <- ref
         n <- name
         as <- parens (commaSepBy1 portArg)
         e <- Toolkit.location
         pure ((newFC s e), n, mkApp f as)
  where
    mkApp : AST
         -> List1 (FileContext, AST)
         -> AST
    mkApp f ((fc, a):::as)
      = foldl (\acc, (fc,a) => App fc acc a) (App fc f a) as

mutual
  cond : Rule AST
  cond
    = do s <- Toolkit.location
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
         e <- Toolkit.location
         pure (IfThenElse (newFC s e) (snd c) t f)

  data MBody = Expr AST
             | TDef (FileContext, String, AST)
             | Bindable (FileContext, String, AST)


  entry : Rule MBody
  entry = (entry' <* symbol ";")
      <|> (do {c <- cond; pure (Expr c)})
      <|> (do {m <- moduleDef; pure (Bindable m)})
    where
      entry' : Rule MBody
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

  entries : Bool -> Rule AST
  entries True
      = do es <- some entry
           m <- endModule
           pure (collapse m es)
  entries False
      = do es <- some entry
           l <- Toolkit.location
           pure (collapse (UnitVal (newFC l l)) es)


  moduleDefGen : Rule String -> Rule (FileContext, String, AST)
  moduleDefGen p
      = do s <- Toolkit.location
           keyword "module"
           n <- p
           value <- moduleFunc
           e <- Toolkit.location
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

      moduleFunc : Rule AST
      moduleFunc = do s <- Toolkit.location
                      xs <- ports
                      e1 <- Toolkit.location
                      symbol ";"
                      es <- (entries True <|> endModule)
                      e <- Toolkit.location
                      pure (buildFunc (newFC s e1) (newFC s e) es xs)

  moduleDef : Rule (FileContext, String, AST)
  moduleDef = moduleDefGen name

data Decl = TDecl (FileContext, String, AST)
          | MDecl (FileContext, String, AST)

decls : RuleEmpty (List Decl)
decls = many (do {m <- moduleDef; pure (MDecl m)}
          <|> do {t <- typeDef <* symbol ";"; pure (TDecl t)})

top : Rule Decl
top
    = do m <- moduleDefGen isTop
         pure (MDecl m)
  where
    isTop : Rule String
    isTop = do keyword "Top"
               pure "Top"

design : Rule AST
design = do ds <- decls
            t <- top
            e <- Toolkit.location
            pure (foldDecls (appTop (newFC e e))
                            (ds ++ [t]))
  where
    foldDecl : Decl -> AST -> AST
    foldDecl (TDecl (fc, n, expr)) body = Let fc n expr body
    foldDecl (MDecl (fc, n, expr)) body = Let fc n expr body

    foldDecls : AST
             -> List Decl
             -> AST
    foldDecls = foldr foldDecl


    appTop : FileContext -> AST
    appTop loc = App loc
                     (Ref (MkRef loc "Top"))
                     (UnitVal loc)

namespace Core

  export
  fromFile : (fname : String)
                   -> IO (Either (ParseError Token) AST)
  fromFile fname
    = case !(parseFile SystemVLexer design fname) of
        Left err  => pure (Left err)
        Right ast => pure (Right (setFileName fname ast))

-- [ EOF ]
