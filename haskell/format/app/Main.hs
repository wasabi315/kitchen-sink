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

type family Snoc xs x where
  Snoc '[] x = '[x]
  Snoc (x ': xs) y = x ': Snoc xs y

type CharToSymbol c = ConsSymbol c ""

type SnocSymbol s c = AppendSymbol s (CharToSymbol c)

type Split c s = SplitAux c "" (UnconsSymbol s)

type family SplitAux c acc s where
  SplitAux c acc 'Nothing = '(acc, "")
  SplitAux c acc ('Just '(c, s)) = '(acc, s)
  SplitAux c acc ('Just '(c', s)) = SplitAux c (SnocSymbol acc c') (UnconsSymbol s)

type Parse s = ParseAux1 '[] (Split '%' s)

type family ParseAux1 acc s where
  ParseAux1 acc '(s, s') = ParseAux2 (Snoc acc (Left s)) (UnconsSymbol s')

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

type FormatFun :: [Either Symbol Char] -> Type -> Type -> Constraint
class FormatFun fmt a f where
  formatFun :: ShowS -> (ShowS -> a) -> f

instance (a ~ b) => FormatFun '[] a b where
  formatFun acc k = k acc

instance (KnownSymbol s, FormatFun fmt a f) => FormatFun (Left s ': fmt) a f where
  formatFun acc = formatFun @fmt (acc . showString (symbolVal @s Proxy))

instance (g ~ (x -> f), FormatArg c x, FormatFun fmt a f) => FormatFun (Right c ': fmt) a g where
  formatFun acc k arg = formatFun @fmt (acc . formatArg @c arg) k

type Kprintf s = FormatFun (Parse s)

kprintf :: (ShowS -> a) -> forall s -> (Kprintf s a f) => f
kprintf k s = formatFun @(Parse s) id k

--------------------------------------------------------------------------------

ksprintf :: (String -> a) -> forall s -> (Kprintf s a f) => f
ksprintf k = kprintf \s -> k (s "")

sprintf :: forall s -> (Kprintf s String f) => f
sprintf = ksprintf id

--------------------------------------------------------------------------------

khprintf :: ((Handle -> IO ()) -> a) -> forall s -> (Kprintf s a f) => f
khprintf k = kprintf \s -> k \h -> hPutStr h (s "")

hprintf :: forall s -> (Kprintf s (Handle -> IO ()) f) => f
hprintf = khprintf id

fprintf :: Handle -> forall s -> (Kprintf s (IO ()) f) => f
fprintf h = khprintf ($ h)

kfprintf :: (Handle -> IO ()) -> Handle -> forall s -> (Kprintf s (IO ()) f) => f
kfprintf k h = khprintf \f -> f h *> k h

printf :: forall s -> (Kprintf s (IO ()) f) => f
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
