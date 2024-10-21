{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Control.Arrow.Effect.State
  ( State (..),
    get,
    put,
    runState,
  )
where

import Control.Arrow.Effect
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------

data State s a b where
  Get :: State s () s
  Put :: State s s ()

get :: Eff (State s) () s
get = Op Get

put :: Eff (State s) s ()
put = Op Put

--------------------------------------------------------------------------------

newtype StateC s a b c = StateC {unStateC :: a (b, s) (c, s)}

instance (Category a) => Category (StateC s a) where
  id = StateC id
  StateC f . StateC g = StateC (f . g)

instance (Arrow a) => Arrow (StateC s a) where
  arr f = StateC (arr \ ~(b, s) -> (f b, s))
  first (StateC f) = StateC (swp >>> first f >>> swp)

swp :: (Arrow a) => a ((b, c), d) ((b, d), c)
swp = arr \ ~(~(b, c), d) -> ((b, d), c)

runState :: (Arrow a) => Eff (State s) b c -> a (b, s) (c, s)
runState =
  unStateC . interpret \case
    Get -> StateC $ arr \ ~(_, s) -> (s, s)
    Put -> StateC $ arr \ ~(s, _) -> ((), s)
