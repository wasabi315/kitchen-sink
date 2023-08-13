{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Comonad
import Control.Comonad.Representable.Store
import Control.Monad
import Data.Bitraversable
import Data.Finite qualified as F
import Data.Function
import Data.Functor.Compose
import Data.Functor.Identity
import Data.List (intersperse, (!!))
import Data.Maybe
import Data.Proxy
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder qualified as TB
import Data.Vector.Sized qualified as V
import GHC.TypeLits

main :: IO ()
main = T.getContents >>= T.putStrLn . typogram

-- Zipper on 2D vector
newtype Z2 n m a = Z2 (Store (V.Vector n `Compose` V.Vector m) a)
  deriving newtype (Functor)

instance (KnownNat n, KnownNat m) => Comonad (Z2 n m) where
  extract (Z2 w) = extract w
  duplicate (Z2 w) = Z2 $ extend Z2 w
  extend f (Z2 w) = Z2 $ extend (f . Z2) w

-- 3x3 window
data Window = W
  { ul :: Char,
    u :: Char,
    ur :: Char,
    l :: Char,
    c :: Char,
    r :: Char,
    dl :: Char,
    d :: Char,
    dr :: Char
  }

currWindow :: (KnownNat n, KnownNat m) => Z2 n m Char -> Window
currWindow (Z2 zz) =
  W
    { ul = ix (decr, decr) zz,
      u = ix (decr, pure) zz,
      ur = ix (decr, incr) zz,
      l = ix (pure, decr) zz,
      c = ix (pure, pure) zz,
      r = ix (pure, incr) zz,
      dl = ix (incr, decr) zz,
      d = ix (incr, pure) zz,
      dr = ix (incr, incr) zz
    }
  where
    ix (f, g) = fromMaybe '\0' . experiment (bitraverse f g)
    incr n = succ n <$ guard (n /= maxBound)
    decr n = pred n <$ guard (n /= minBound)

convert :: (KnownNat n, KnownNat m) => Z2 n m Char -> Z2 n m Char
convert = extend (conv . currWindow)
  where
    conv = \case
      W {c = '+', u = '|', l = '-', r = '-', d = '|'} -> '┼'
      W {c = '+', l = '-', r = '-', d = '|'} -> '┬'
      W {c = '+', u = '|', r = '-', d = '|'} -> '├'
      W {c = '+', u = '|', l = '-', d = '|'} -> '┤'
      W {c = '+', u = '|', l = '-', r = '-'} -> '┴'
      W {c = '-', d = '|'} -> '┬'
      W {c = '|', r = '-'} -> '├'
      W {c = '|', l = '-'} -> '┤'
      W {c = '-', u = '|'} -> '┴'
      W {c = '+', r = '-', d = '|'} -> '┌'
      W {c = '+', l = '-', d = '|'} -> '┐'
      W {c = '+', u = '|', l = '-'} -> '┘'
      W {c = '+', u = '|', r = '-'} -> '└'
      W {c = '.', r = '-', d = '|'} -> '╭'
      W {c = '.', l = '-', d = '|'} -> '╮'
      W {c = '.', u = '|', l = '-'} -> '╯'
      W {c = '.', u = '|', r = '-'} -> '╰'
      W {c = '\'', u = '|', l = '-'} -> '╯'
      W {c = '\'', u = '|', r = '-'} -> '╰'
      W {c = '^', d = '|'} -> '▲'
      W {c = 'v', u = '|'} -> '▼'
      W {c = '<', r = '-'} -> '◀'
      W {c = '>', l = '-'} -> '▶'
      W {c = c} -> c

textToZ2 :: T.Text -> r -> (forall h w. (KnownNat h, KnownNat w) => Z2 h w Char -> r) -> r
textToZ2 t r k
  | T.null t = r
  | ts <- T.lines t,
    h <- length ts,
    w <- maximum $ map T.length ts,
    Just (SomeNat (_ :: Proxy h)) <- someNatVal (fromIntegral h),
    Just (SomeNat (_ :: Proxy w)) <- someNatVal (fromIntegral w) =
      k . Z2 @h @w . flip store minBound $ \(E i, E j) ->
        let row = ts !! i
         in if j >= T.length row then ' ' else T.index row j
  | otherwise = error "impossible"

pattern E :: Enum a => Int -> a
pattern E n <- (fromEnum -> n) where E n = toEnum n

z2ToText :: (KnownNat h, KnownNat w) => Z2 h w Char -> T.Text
z2ToText (Z2 (StoreT (Identity (Compose css)) _)) =
  css
    & fmap (foldMap TB.singleton)
    & V.toList
    & intersperse (TB.singleton '\n')
    & mconcat
    & TB.toLazyText
    & TL.toStrict

typogram :: T.Text -> T.Text
typogram txt
  | T.null txt = txt
  | otherwise = textToZ2 txt T.empty (z2ToText . convert)
