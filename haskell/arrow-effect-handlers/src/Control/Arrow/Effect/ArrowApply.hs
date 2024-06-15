{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}

module Control.Arrow.Effect.ArrowApply
  ( Eff (..),
    Handler (..),
    handleWith,
    interpret,
  )
where

import Control.Arrow
import Control.Arrow.Effect (Eff (..))
import Prelude hiding (id, (.))

data Handler op a c d = Handler
  { valh :: a c d,
    effh :: forall i o. op i o -> a o d -> a i d -- Note no @x@
  }

handleWith ::
  forall op a b c d.
  (ArrowApply a) =>
  Handler op a c d ->
  Eff op b c ->
  a b d
handleWith Handler {..} m = run m valh
  where
    run :: forall i o. Eff op i o -> a o d -> a i d
    run (Arr f) k = arr f >>> k
    run (Op e) k = effh e k
    run (Comp f g) k = run g (run f k)
    -- We can cheat a bit if @a@ is an instance of ArrowApply
    run (First f) k = arr (\(i, x) -> (run f (arr (,x) >>> k), i)) >>> app

interpret :: (ArrowApply a) => (forall i o. e i o -> a i o) -> Eff e b c -> a b c
interpret f =
  handleWith Handler {valh = returnA, effh = \eff k -> f eff >>> k}
