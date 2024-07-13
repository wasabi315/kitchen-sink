{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
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
import Text.Show.Functions ()

--------------------------------------------------------------------------------
-- Parser

type family Snoc xs x where
  Snoc '[] x = '[x]
  Snoc (x ': xs) y = x ': Snoc xs y

type CharToSymbol c = ConsSymbol c ""

type SnocSymbol s c = AppendSymbol s (CharToSymbol c)

type Split c s = SplitAux c "" (UnconsSymbol s)

type family SplitAux c acc s where
  SplitAux c acc Nothing = '(acc, "")
  SplitAux c acc (Just '(c, s)) = '(acc, s)
  SplitAux c acc (Just '(c', s)) = SplitAux c (SnocSymbol acc c') (UnconsSymbol s)

type Parse s = ParseAux1 '[] (Split '%' s)

type family ParseAux1 acc s where
  ParseAux1 acc '(s, s') = ParseAux2 (Snoc acc (Left s)) (UnconsSymbol s')

type family ParseAux2 acc s where
  ParseAux2 acc Nothing = acc
  ParseAux2 acc (Just '( '%', s)) = ParseAux1 (Snoc acc (Left (CharToSymbol '%'))) (Split '%' s)
  ParseAux2 acc (Just '(c, s)) = ParseAux1 (Snoc acc (Right c)) (Split '%' s)

--------------------------------------------------------------------------------

type FormatArg :: Char -> Type -> Constraint
class FormatArg c a where
  formatArg :: a -> String

instance (Integral a) => FormatArg 'd' a where
  formatArg = show @Integer . fromIntegral

instance (a ~ String) => FormatArg 's' a where
  formatArg = id

type UnsupportedFormatSpecifierMsg c = 'Text "Unsupported format specifier: " :<>: 'ShowType c

instance {-# OVERLAPPABLE #-} (Unsatisfiable (UnsupportedFormatSpecifierMsg c)) => FormatArg c a where
  formatArg = unsatisfiable

data Format f a where
  End :: Format a a
  Str :: String -> Format f a -> Format f a
  Hole :: (x -> String) -> Format f a -> Format (x -> f) a

deriving instance Show (Format f a)

infixr 5 @@

(@@) :: Format a b -> Format b c -> Format a c
End @@ fmt' = fmt'
Str s fmt @@ fmt' = Str s (fmt @@ fmt')
Hole f fmt @@ fmt' = Hole f (fmt @@ fmt')

type ToFormat' :: [Either Symbol Char] -> Type -> Type -> Constraint
class ToFormat' fmt f a where
  toFormat' :: Format f a

instance (a ~ b) => ToFormat' '[] a b where
  toFormat' = End

instance (KnownSymbol s, ToFormat' fmt f a) => ToFormat' (Left s ': fmt) f a where
  toFormat' = Str (symbolVal @s Proxy) (toFormat' @fmt)

instance (g ~ (x -> f), FormatArg c x, ToFormat' fmt f a) => ToFormat' (Right c ': fmt) g a where
  toFormat' = Hole (formatArg @c) (toFormat' @fmt)

type ToFormat s = ToFormat' (Parse s)

toFormat :: forall s -> (ToFormat s f a) => Format f a
toFormat s = toFormat' @(Parse s)

--------------------------------------------------------------------------------

ksprintf' :: (String -> a) -> Format f a -> f
ksprintf' k End = k ""
ksprintf' k (Str s fmt) = ksprintf' (\s' -> k (s ++ s')) fmt
ksprintf' k (Hole f fmt) = \x -> ksprintf' (\s -> k (f x ++ s)) fmt

ksprintf :: (String -> a) -> forall s -> (ToFormat s f a) => f
ksprintf k s = ksprintf' k (toFormat s)

sprintf :: forall s -> (ToFormat s f String) => f
sprintf = ksprintf id

khprintf :: ((Handle -> IO ()) -> a) -> forall s -> (ToFormat s f a) => f
khprintf k = ksprintf \s -> k \h -> hPutStr h s

hprintf :: forall s -> (ToFormat s f (Handle -> IO ())) => f
hprintf = khprintf id

kfprintf :: (Handle -> IO ()) -> Handle -> forall s -> (ToFormat s f (IO ())) => f
kfprintf k h = khprintf \f -> f h *> k h

fprintf :: Handle -> forall s -> (ToFormat s f (IO ())) => f
fprintf = kfprintf \_ -> pure ()

printf :: forall s -> (ToFormat s f (IO ())) => f
printf = fprintf stdout

--------------------------------------------------------------------------------

data LogLevel = Debug | Info | Warning | Error

log' :: LogLevel -> forall s -> (ToFormat s f (IO ())) => f
log' lvl = khprintf \f -> do
  let prefix = case lvl of
        Debug -> "\ESC[0;32m[DEBUG]: "
        Info -> "\ESC[0;34m[INFO]: "
        Warning -> "\ESC[0;33m[WARN]: "
        Error -> "\ESC[0;31m[ERR]: "
  hPutStr stderr prefix *> f stderr *> hPutStr stderr "\ESC[0m"

--------------------------------------------------------------------------------

main :: IO ()
main = do
  khprintf
    (\f -> f stdout *> f stderr)
    "%d + %d\n"
    (1 :: Int)
    (2 :: Int)
  log' Debug "Hello, %s!\n" "world"
  log' Error "Main.hs:%d:%d undefined variable: %s\n" 100 42 "x"
