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
import GHC.TypeLits
import System.IO

--------------------------------------------------------------------------------
-- Parser

type Snoc :: [a] -> a -> [a]
type family Snoc xs x where
  Snoc '[] x = '[x]
  Snoc (x ': xs) y = x ': Snoc xs y

type SnocSymbol :: Symbol -> Char -> Symbol
type SnocSymbol s c = AppendSymbol s (ConsSymbol c "")

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
  ParseAux2 acc ('Just '(c, s)) = ParseAux1 (Snoc acc (Right c)) (Split '%' s)

--------------------------------------------------------------------------------

type FormatArg :: Char -> Type -> Constraint
class FormatArg c a where
  formatArg :: a -> ShowS

instance (Integral a) => FormatArg 'd' a where
  formatArg = shows @Integer . fromIntegral

instance (a ~ String) => FormatArg 's' a where
  formatArg = showString

--------------------------------------------------------------------------------

type FormatFun :: [Either Symbol Char] -> Type -> Type -> Constraint
class FormatFun fmt k f where
  formatFun :: ShowS -> k -> f

instance (a ~ b) => FormatFun '[] (String -> a) b where
  formatFun acc k = k (acc "")

instance (a ~ (), b ~ c) => FormatFun '[] (IO a -> b) c where
  formatFun acc k = k $ putStr (acc "")

instance (a ~ (), b ~ c) => FormatFun '[] ((Handle -> IO a) -> b) c where
  formatFun acc k = k \h -> hPutStr h (acc "")

instance (KnownSymbol s, FormatFun fmt k f) => FormatFun (Left s ': fmt) k f where
  formatFun acc = formatFun @fmt (acc . showString (symbolVal @s Proxy))

instance (g ~ (a -> f), FormatArg c a, FormatFun fmt k f) => FormatFun (Right c ': fmt) k g where
  formatFun acc k arg = formatFun @fmt (acc . formatArg @c arg) k

--------------------------------------------------------------------------------

type KPrintf :: Symbol -> Type -> Type -> Constraint
class KPrintf s k f where
  kprintf :: k -> forall s' -> (s ~ s') => f

instance (Parse s ~ fmt, FormatFun fmt k f) => KPrintf s k f where
  kprintf k _ = formatFun @fmt id k

--------------------------------------------------------------------------------

main :: IO ()
main = do
  kprintf (\f -> f stdout *> f stderr :: IO ())
    "%d + %d\n"
    (1 :: Int)
    (2 :: Int)
  kprintf (\f h -> f (h :: Handle) :: IO ())
    "Hello, %s!\n"
    "wasabi"
    stdout
