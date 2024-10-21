{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Control.Arrow.Effect.Reader
  ( Reader (..),
    ask,
    local,
    runReader,
  )
where

import Control.Arrow.Effect
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------

data Reader r a b where
  Ask :: Reader r () r
  Local :: (r -> r) -> Eff (Reader r) a b -> Reader r a b

ask :: Eff (Reader r) () r
ask = Op Ask

local :: (r -> r) -> Eff (Reader r) a b -> Eff (Reader r) a b
local f a = Op (Local f a)

--------------------------------------------------------------------------------

newtype ReaderC r a b c = ReaderC {unReaderC :: a (b, r) c}

instance (Arrow a) => Category (ReaderC r a) where
  id = ReaderC $ arr fst
  ReaderC f . ReaderC g = ReaderC (f . first g . arr dup)

dup :: (Arrow a) => a (b, c) ((b, c), c)
dup = arr \ ~(b, c) -> ((b, c), c)

swp :: (Arrow a) => a ((b, c), d) ((b, d), c)
swp = arr \ ~(~(b, c), d) -> ((b, d), c)

instance (Arrow a) => Arrow (ReaderC r a) where
  arr f = ReaderC $ arr (f . fst)
  first (ReaderC f) = ReaderC (swp >>> first f)

runReader :: (Arrow a) => Eff (Reader r) b c -> a (b, r) c
runReader =
  unReaderC . interpret \case
    Ask -> ReaderC $ arr snd
    Local f a -> ReaderC $ arr (second f) >>> runReader a
