{-# LANGUAGE OverloadedStrings #-}

module TypedTC.Parser (
    parseStatement,
    Expr (..),
    PType (..),
    Identifier (..),
    TypeAssume (..),
    Statement (..),
) where

import Prelude hiding (exp, pi, succ)

import Control.Monad (guard)
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Data.Foldable (asum)
import Data.Functor (void)
import Data.List.NonEmpty qualified as NE
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Numeric.Natural (Natural)
import Text.Megaparsec
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import Text.Megaparsec.Char.Lexer (decimal)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

keyword :: Text -> Parser Text
keyword k = lexeme (string k <* notFollowedBy alphaNumChar)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

newtype Identifier = Identifier Text
    deriving (Eq, Show, IsString)

data Expr
    = LiteralNat Natural
    | LiteralBool Bool
    | If Expr Expr Expr
    | Succ Expr
    | NatElim Expr Expr Expr
    | Lambda (NE.NonEmpty (Identifier, PType)) Expr
    | Var Identifier
    | App Expr Expr
    deriving (Eq, Show)

data PType
    = PNat
    | PBool
    | PFun PType PType
    deriving (Eq, Show)

data TypeAssume = TypeAssume Identifier PType
    deriving (Eq, Show)

data Statement
    = StAssume (NE.NonEmpty TypeAssume)
    | StLet Identifier Expr
    | StExpr Expr
    deriving (Eq, Show)

symbols :: [Text] -> Parser Text
symbols = asum . map symbol

syntax :: [Text] -> Parser ()
syntax = void . symbols

arrowSym :: Parser ()
arrowSym = syntax ["->", "→"] <?> "→"

lambdaSym :: Parser ()
lambdaSym = syntax ["\\", "λ"] <?> "λ"

assumeSym :: Parser ()
assumeSym = syntax ["assume"]

ofTypeSym :: Parser ()
ofTypeSym = syntax ["::"]

assume :: Parser Statement
assume = StAssume <$> (assumeSym *> parser)
  where
    parser =
        NE.singleton <$> try typeAssumeParser
            <|> NE.some1 (parens typeAssumeParser)

statementParser :: Parser Statement
statementParser = sc *> (assume <|> letP <|> StExpr <$> expression) <* eof

letP :: Parser Statement
letP =
    StLet
        <$> (sc *> keyword "let" *> identifier)
        <*> (symbol "=" *> expression)

identifier :: Parser Identifier
identifier =
    Identifier <$> lexeme name
  where
    name :: Parser Text
    name = do
        start <- letterChar <|> char '_'
        more <- many alphaNumChar
        let res = T.pack (start : more)
        guard (res `notElem` reservedWords)
        pure res

reservedWords :: [Text]
reservedWords = ["if", "then", "else", "Nat", "Bool", "True", "False", "λ"]

typeAssumeParser :: Parser TypeAssume
typeAssumeParser = TypeAssume <$> (identifier <* ofTypeSym) <*> typeP

literalNat :: Parser Expr
literalNat = LiteralNat <$> lexeme (decimal <* notFollowedBy alphaNumChar)

literalBool :: Parser Expr
literalBool =
    LiteralBool <$> (True <$ keyword "True" <|> False <$ keyword "False")

lambda :: Parser Expr
lambda = do
    lambdaSym
    args <- NE.some1 (parens lambdaArg)
    arrowSym
    Lambda args <$> exp

lambdaArg :: Parser (Identifier, PType)
lambdaArg = (,) <$> identifier <* ofTypeSym <*> typeP

typeP :: Parser PType
typeP = makeExprParser typeTerm table
  where
    typeTerm =
        PNat <$ keyword "Nat"
            <|> PBool <$ keyword "Bool"
    table :: [[Operator Parser PType]]
    table = [[InfixR $ PFun <$ arrowSym]]

ifP :: Parser Expr
ifP =
    If
        <$> (keyword "if" *> exp)
        <*> (keyword "then" *> exp)
        <*> (keyword "else" *> exp)

succP :: Parser Expr
succP = Succ <$> (keyword "Succ" *> term)

natElim :: Parser Expr
natElim = NatElim <$> (keyword "natElim" *> term) <*> term <*> term

expression :: Parser Expr
expression = sc *> exp

exp :: Parser Expr
exp = makeExprParser term table
  where
    table :: [[Operator Parser Expr]]
    table =
        [
            [ InfixL (pure App)
            ]
        ]

term :: Parser Expr
term =
    parens exp
        <|> literalNat
        <|> literalBool
        <|> try ifP
        <|> try succP
        <|> try natElim
        <|> lambda
        <|> Var <$> try identifier

parseStatement :: Text -> Either (ParseErrorBundle Text Void) Statement
parseStatement = runParser statementParser "input"
