{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Arrow.Effect.MoreInputs (Eff (..), Handler (..), handleWith) where

import Control.Arrow
import Control.Arrow.Effect (Eff (..))
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Effectful Arrows and Handlers

data Handler op a i' c d = Handler
  { valh :: a (c, i') d,
    effh :: forall i o x. op i o -> a (o, i', x) d -> a (i, i', x) d -- Note @i'@
  }

handleWith ::
  forall op a e s i' c d.
  (Arrow a) =>
  Handler op a i' c d ->
  Eff op (e, s) c ->
  a (e, (i', s)) d
handleWith Handler {..} m =
  arr (\(e, (i', s)) -> ((e, s), i', ()))
    >>> run m (arr (\(c, i', ()) -> (c, i')) >>> valh)
  where
    run :: forall i o x. Eff op i o -> a (o, i', x) d -> a (i, i', x) d
    run (Arr f) k = arr (\(i, i', x) -> (f i, i', x)) >>> k
    run (Op e) k = effh e k
    run (Comp f g) k = run g (run f k)
    run (First f) k =
      arr (\((i, x'), i', x) -> (i, i', (x', x)))
        >>> run f (arr (\(o, i', (x', x)) -> ((o, x'), i', x)) >>> k)
