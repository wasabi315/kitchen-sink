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

newtype ReaderC r a b c = ReaderC {unReaderC :: a (r, b) c}

instance (Arrow a) => Category (ReaderC r a) where
  id = ReaderC $ arr snd
  ReaderC f . ReaderC g = ReaderC (arr (\ ~(r, b) -> (r, (r, b))) >>> second g >>> f)

instance (Arrow a) => Arrow (ReaderC r a) where
  arr f = ReaderC $ arr (f . snd)
  first (ReaderC f) = ReaderC (unassoc >>> first f)

runReader :: (Arrow a) => Eff (Reader r) b c -> a (r, b) c
runReader =
  unReaderC . interpret \case
    Ask -> ReaderC $ arr fst
    Local f a -> ReaderC $ arr (first f) >>> runReader a
