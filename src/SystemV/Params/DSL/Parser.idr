module SystemV.Params.DSL.Parser

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

import        SystemV.Common.Types.Direction
import        SystemV.Common.Types.Gate
import        SystemV.Common.Types.Nat.Arithmetic
import        SystemV.Common.Types.Nat.Comparison
import        SystemV.Common.Types.Boolean

import        SystemV.Common.Parser.Direction
import        SystemV.Common.Parser.Gate
import        SystemV.Common.Parser.Arithmetic
import        SystemV.Common.Parser.Boolean


import        SystemV.Params.DSL.AST.Raw

%default total -- is actually covering but portArg cannot pass.

ref : Rule Token AST
ref = inserts rawRef Ref

number : Rule Token AST
number = inserts Arithmetic.expr AExpr

boolean : Rule Token AST
boolean = inserts Boolean.expr BExpr

logic : Rule Token AST
logic = WithFileContext.gives "logic" TyLogic

array : Rule Token AST
array = do
  s <- location
  ty <- ref <|> logic
  symbol "["
  commit
  idx <- number
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

ports : Rule Token (List (FileContext, String, AST))
ports =  symbol "(" *> symbol ")" *> pure Nil
     <|> do {p <- parens (commaSepBy1 port); pure (forget p)}

  where
    port : Rule Token (FileContext, String, AST)
    port
      = do st <- location
           d <- direction
           keyword "wire"
           t <- type_
           label <- name
           e <- location
           pure (newFC st e, label, TyPort (newFC st e) t d)

params : Rule Token (List (FileContext, String, AST, AST))
params
    = do symbol "#"
         ps <- parens (commaSepBy1 param)
         pure (forget ps)
  where
      paramVal : Rule Token AST
      paramVal = inserts (WithFileContext.inserts natLit NatV) AExpr  <|> type_

      paramTy : Rule Token AST
      paramTy =  WithFileContext.gives "nat"      TyNat
             <|> WithFileContext.gives "datatype" TyDATA

      param : Rule Token (FileContext, String, AST, AST)
      param
          = do s <- location
               keyword "parameter"
               ty <- paramTy
               l <- name
               symbol "="
               v <- paramVal
               e <- location
               pure (newFC s e, l, ty, v)


mutual
  portArg : Rule Token (FileContext, AST)
  portArg =   (do r <- ref; pure (getFC r, r))
          <|> writeTo
          <|> readFrom
          <|> cast
          <|> slice
          <|> index
    where
      writeTo : Rule Token (FileContext, AST)
      writeTo
        = do s <- location
             symbol "("
             keyword "writeTo"
             p <- portArg
             symbol ")"
             e <- location
             pure (newFC s e, WriteTo (newFC s e) (snd p))

      readFrom : Rule Token (FileContext, AST)
      readFrom
        = do s <- location
             symbol "("
             keyword "readFrom"
             p <- portArg
             symbol ")"
             e <- location
             pure (newFC s e, ReadFrom (newFC s e) (snd p))

      index : Rule Token (FileContext, AST)
      index
        = do s <- location
             symbol "("
             keyword "index"
             n <- (number <|> size)
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
             a <- (number <|> size)
             o <- (number <|> size)
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

  size : Rule Token AST
  size
      = inserts body Size
    where
      body : Rule Token AST
      body
        = do keyword "size"
             p <- portArg
             pure (snd p)

portArgs : Rule Token (List1 (FileContext, AST))
portArgs = parens (commaSepBy1 portArg)



paramArgs : Rule Token (List1 (FileContext, (String, AST)))
paramArgs
    = do symbol "#"
         parens (commaSepBy1 paramArg)
  where
    paramArg : Rule Token (FileContext, String, AST)
    paramArg
      = do l <- location
           n <- name
           symbol "="
           v <- (number <|> size <|> type_)
           e <- location
           pure (newFC l e, n,v)


driveCatch : Rule Token AST
driveCatch = inserts (do p <- (keyword "drive" *> portArg); pure (snd p))  Drive
         <|> inserts (do p <- (keyword "catch" *> portArg); pure (snd p)) Catch

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



moduleInst : Rule Token (FileContext, String, AST)
moduleInst
    = do s <- location
         f <- portArg
         ps <- optional paramArgs
         n <- name
         as <- portArgs
         e <- location
         pure ((newFC s e), n, App (newFC s e) (snd f) ps as)

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

mutual
  cond : Rule Token AST
  cond
      = do s <- location
           keyword "if"
           commit
           c <- (pArg <|> boolean)
           keyword "begin"
           t <- entries False
           keyword "end"
           keyword "else"
           keyword "begin"
           f <- entries False
           keyword "end"
           e <- location
           pure (IfThenElse (newFC s e) c t f)
    where
      pArg : Rule Token AST
      pArg
        = do p <- portArg
             pure (snd p)

  for : Rule Token AST
  for
    = do s <- location
         keyword "for"
         n <- parens (do {i <- name; symbol "="; n <- (number <|> size); pure (i,n)})
         keyword "begin"
         b <- (entries False)
         keyword "end"
         e <- location
         pure (For (newFC s e) (fst n) (snd n) b)


  data MBody = Expr AST
             | TDef (FileContext, String, AST)
             | Bindable (FileContext, String, AST)



  entry : Rule Token MBody
  entry = (entry' <* symbol ";")
      <|> (do {c <- (cond <|> for); pure (Expr c)})
      <|> (do {m <- moduleDef; pure (Bindable m)})
    where
      entry' : Rule Token MBody
      entry' = (do { e <- expr;                     pure (Expr     e)})
           <|> (do { d <- typeDef;                  pure (TDef     d)})
           <|> (do { c <- (chanDef <|> moduleInst); pure (Bindable c)})

  collapse : AST -> List MBody -> AST
  collapse l xs
      = foldr foldEntry l xs
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
           pure (collapse m (forget es))
  entries False
      = do es <- some entry
           l <- location
           pure (collapse (UnitVal (newFC l l)) (forget es))


  moduleDefGen : Rule Token String -> Rule Token (FileContext, String, AST)
  moduleDefGen p
      = do s <- location
           keyword "module"
           n <- p
           value <- moduleFunc
           e <- location
           pure (newFC s e, n, value)
    where

      moduleFunc : Rule Token AST
      moduleFunc = do s <- location
                      as <- option Nil params
                      ps <- ports
                      symbol ";"
                      body <- ((entries True) <|> endModule)
                      e <- location
                      pure (Func (newFC s e) as ps body)

  moduleDef : Rule Token (FileContext, String, AST)
  moduleDef = moduleDefGen name

data Decl = TDecl (FileContext, String, AST)
          | MDecl (FileContext, String, AST)

decls : RuleEmpty Token (List Decl)
decls = many (do {m <- moduleDef; pure (MDecl m)}
          <|> do {t <- typeDef <* symbol ";"; pure (TDecl t)})

top : Rule Token Decl
top
    = do m <- moduleDefGen isTop
         pure (MDecl m)
  where
    isTop : Rule Token String
    isTop = do keyword "Top"
               pure "Top"

design : Rule Token AST
design = do ds <- decls
            t <- top
            e <- location
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
                     Nothing
                     ((loc, UnitVal loc) ::: Nil)


namespace Params
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
