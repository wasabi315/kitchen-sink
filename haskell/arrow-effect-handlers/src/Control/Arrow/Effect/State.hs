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

newtype StateC s a b c = StateC {unStateC :: a (s, b) (s, c)}

instance (Category a) => Category (StateC s a) where
  id = StateC id
  StateC f . StateC g = StateC (f . g)

instance (Arrow a) => Arrow (StateC s a) where
  arr f = StateC (arr \(s, b) -> (s, f b))
  first (StateC f) = StateC (unassoc >>> first f >>> assoc)

runState :: (Arrow a) => Eff (State s) b c -> a (s, b) (s, c)
runState =
  unStateC . interpret \case
    Get -> StateC $ arr \ ~(s, _) -> (s, s)
    Put -> StateC $ arr \ ~(_, s) -> (s, ())
