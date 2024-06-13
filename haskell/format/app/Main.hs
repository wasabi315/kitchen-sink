{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Kind
import Data.Proxy
import GHC.TypeError
import GHC.TypeLits
import System.IO

--------------------------------------------------------------------------------
-- Parser

type Snoc :: [a] -> a -> [a]
type family Snoc xs x where
  Snoc '[] x = '[x]
  Snoc (x ': xs) y = x ': Snoc xs y

type CharToSymbol :: Char -> Symbol
type CharToSymbol c = ConsSymbol c ""

type SnocSymbol :: Symbol -> Char -> Symbol
type SnocSymbol s c = AppendSymbol s (CharToSymbol c)

type Split :: Char -> Symbol -> (Symbol, Symbol)
type Split c s = SplitAux c "" (UnconsSymbol s)

type SplitAux :: Char -> Symbol -> Maybe (Char, Symbol) -> (Symbol, Symbol)
type family SplitAux c acc s where
  SplitAux c acc 'Nothing = '(acc, "")
  SplitAux c acc ('Just '(c, s)) = '(acc, s)
  SplitAux c acc ('Just '(c', s)) = SplitAux c (SnocSymbol acc c') (UnconsSymbol s)

type Parse :: Symbol -> [Either Symbol Char]
type Parse s = ParseAux1 '[] (Split '%' s)

type ParseAux1 :: [Either Symbol Char] -> (Symbol, Symbol) -> [Either Symbol Char]
type family ParseAux1 acc s where
  ParseAux1 acc '(s, s') = ParseAux2 (Snoc acc (Left s)) (UnconsSymbol s')

type ParseAux2 :: [Either Symbol Char] -> Maybe (Char, Symbol) -> [Either Symbol Char]
type family ParseAux2 acc s where
  ParseAux2 acc 'Nothing = acc
  ParseAux2 acc ('Just '( '%', s)) = ParseAux1 (Snoc acc (Left (CharToSymbol '%'))) (Split '%' s)
  ParseAux2 acc ('Just '(c, s)) = ParseAux1 (Snoc acc (Right c)) (Split '%' s)

--------------------------------------------------------------------------------

type FormatArg :: Char -> Type -> Constraint
class FormatArg c a where
  formatArg :: a -> ShowS

instance (Integral a) => FormatArg 'd' a where
  formatArg = shows @Integer . fromIntegral

instance (a ~ String) => FormatArg 's' a where
  formatArg = showString

instance {-# OVERLAPPABLE #-} (Unsatisfiable ('Text "Unsupported format specifier: \"" :<>: 'ShowType c :<>: 'Text "\"")) => FormatArg c a where
  formatArg = unsatisfiable

class Output a where
  output :: String -> a

type FormatFun :: [Either Symbol Char] -> Type -> Type -> Constraint
class FormatFun fmt a f where
  formatFun :: (Output r) => ShowS -> (r -> a) -> f

instance (a ~ b) => FormatFun '[] a b where
  formatFun acc k = k (output (acc ""))

instance (KnownSymbol s, FormatFun fmt a f) => FormatFun (Left s ': fmt) a f where
  formatFun acc = formatFun @fmt (acc . showString (symbolVal @s Proxy))

instance (g ~ (b -> f), FormatArg c b, FormatFun fmt a f) => FormatFun (Right c ': fmt) a g where
  formatFun acc k arg = formatFun @fmt (acc . formatArg @c arg) k

type KPrintf :: Symbol -> Type -> Type -> Constraint
type KPrintf s = FormatFun (Parse s)

kprintf :: (Output r) => (r -> a) -> forall s -> (KPrintf s a f) => f
kprintf k s = formatFun @(Parse s) id k

--------------------------------------------------------------------------------

instance Output String where
  output = id

ksprintf :: (String -> a) -> forall s -> (KPrintf s a f) => f
ksprintf = kprintf

sprintf :: forall s -> (KPrintf s String f) => f
sprintf = ksprintf id

--------------------------------------------------------------------------------

instance Output (Handle -> IO ()) where
  output s h = hPutStr h s

khprintf :: ((Handle -> IO ()) -> a) -> forall s -> (KPrintf s a f) => f
khprintf = kprintf

hprintf :: forall s -> (KPrintf s (Handle -> IO ()) f) => f
hprintf = khprintf id

fprintf :: Handle -> forall s -> (KPrintf s (IO ()) f) => f
fprintf h = khprintf \f -> f h

printf :: forall s -> (KPrintf s (IO ()) f) => f
printf = fprintf stdout

--------------------------------------------------------------------------------

main :: IO ()
main = do
  khprintf
    (\f -> f stdout *> f stderr)
    "%d + %d\n"
    (1 :: Int)
    (2 :: Int)
  khprintf
    (\f h -> f h)
    "Hello, %s!\n"
    "world"
    stdout
