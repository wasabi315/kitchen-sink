module Main (module Main) where

import Data.Char
import Data.Function
import Data.MultiSet (MultiSet)
import Data.MultiSet qualified as MS
import Data.String
import Data.Void
import System.IO
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

--------------------------------------------------------------------------------

infixr 5 :*

infixr 4 :->

type Name = String

data Ty
  = Var Name
  | Unit
  | Ty :* Ty
  | Ty :-> Ty
  | List Ty
  deriving (Show)

instance IsString Ty where
  fromString = Var

data Atom
  = AVar Name
  | AList NF
  deriving (Show, Eq, Ord)

data Factor = NF :=> Atom
  deriving (Show, Eq, Ord)

type NF = MultiSet Factor

--------------------------------------------------------------------------------

{-

Original code from the paper:

red :: Ty -> Ty
red (Var x) = Var x
red Unit = Unit
red (a :* b) = case (red a, red b) of
  (Unit, b) -> b
  (a, Unit) -> a
  (a, b) -> a :* b
red (a :-> b) = case (red a, red b) of
  (Unit, a) -> a
  (a, b :-> c) -> (a :* b) :-> c
  (_, Unit) -> Unit
  (a, b :* c) -> red (a :-> b) :* red (a :-> c)
  (a, b) -> a :-> b
red (List a) = List (red a)

chtype :: Ty -> NF
chtype (Var x) = MS.singleton (mempty :=> x)
chtype (x :-> Var y) = MS.singleton (chtype x :=> y)
chtype (_ :-> _) = error "not normal"
chtype Unit = mempty
chtype (a :* b) = chtype a <> chtype b
chtype (List a) = undefined

equiv :: Ty -> Ty -> Bool
equiv a b = chtype (red a) == chtype (red b)

-}

atomic :: Atom -> NF
atomic a = MS.singleton (mempty :=> a)

var :: Name -> NF
var x = atomic (AVar x)

list :: NF -> NF
list a = atomic (AList a)

(-->) :: NF -> NF -> NF
(-->) a = MS.map (\(b :=> x) -> (a <> b) :=> x)

reduce :: Ty -> NF
reduce (Var x) = var x
reduce Unit = mempty
reduce (a :* b) = reduce a <> reduce b
reduce (a :-> b) = reduce a --> reduce b
reduce (List a) = list (reduce a)

equiv :: Ty -> Ty -> Bool
equiv = (==) `on` reduce

--------------------------------------------------------------------------------

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

pName :: Parser Name
pName = lexeme $ takeWhile1P (Just "name") isAlphaNum

pAtom :: Parser Ty
pAtom =
  (Var <$> pName)
    <|> try (Unit <$ symbol "()")
    <|> parens pTy
    <|> brackets (List <$> pTy)

pProd :: Parser Ty
pProd = foldr1 (:*) <$> pAtom `sepBy1` symbol "*"

pTy :: Parser Ty
pTy = foldr1 (:->) <$> pProd `sepBy1` symbol "->"

parseTy :: String -> Maybe Ty
parseTy = parseMaybe (pTy <* eof)

parseSigs :: String -> Maybe [(Name, Ty)]
parseSigs = parseMaybe $ many ((,) <$> pName <*> (symbol ":" *> pTy)) <* eof

prettyTy :: Int -> Ty -> ShowS
prettyTy p = \case
  Var x -> showString x
  Unit -> showString "()"
  a :* b -> showParen (p > 5) $ prettyTy 6 a . showString " * " . prettyTy 5 b
  a :-> b -> showParen (p > 4) $ prettyTy 5 a . showString " -> " . prettyTy 4 b
  List a -> showString "[" . prettyTy 0 a . showString "]"

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  Just sigs <- parseSigs <$> readFile "signatures.txt"
  fix \loop -> do
    putStr "> "
    input <- getLine
    Just query <- pure $ parseTy input
    sigs
      & filter (equiv query . snd)
      & mapM_ (\(x, a) -> putStrLn $ x ++ " : " ++ prettyTy 0 a "")
    loop
