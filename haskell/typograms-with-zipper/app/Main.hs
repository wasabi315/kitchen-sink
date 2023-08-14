{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import Control.Comonad
import Control.Comonad.Representable.Store
import Control.Monad
import Data.Bitraversable
import Data.Function
import Data.Functor.Compose
import Data.Functor.Identity
import Data.List ((!!))
import Data.Maybe
import Data.Proxy
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder qualified as TB
import Data.Vector.Sized qualified as V
import GHC.TypeLits

main :: IO ()
main = T.getContents >>= T.putStr . typogram

-- Zipper on 2D vector
type Z2 n m a = Store (V.Vector n `Compose` V.Vector m) a

-- 3x3 window
data Window = W
  { ul, u, ur :: Char,
    l, c, r :: Char,
    dl, d, dr :: Char
  }

currWindow :: (KnownNat n, KnownNat m) => Z2 n m Char -> Window
currWindow zz =
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
    h <- fromIntegral $ length ts,
    w <- fromIntegral $ maximum $ map T.length ts,
    Just (SomeNat (_ :: Proxy h)) <- someNatVal h,
    Just (SomeNat (_ :: Proxy w)) <- someNatVal w =
      k @h @w $ flip store minBound $ \(i, j) ->
        charAt (ts !! fromEnum i) (fromEnum j)
  where
    charAt t i = if i >= T.length t then ' ' else T.index t i

z2ToText :: (KnownNat h, KnownNat w) => Z2 h w Char -> T.Text
z2ToText (StoreT (Identity (Compose css)) _) =
  css
    & foldMap ((<> TB.singleton '\n') . foldMap TB.singleton)
    & TB.toLazyText
    & TL.toStrict

typogram :: T.Text -> T.Text
typogram txt = textToZ2 txt T.empty (z2ToText . convert)
