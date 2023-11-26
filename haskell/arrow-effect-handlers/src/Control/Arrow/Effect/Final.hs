{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Control.Arrow.Effect.Final
  ( Eff (..),
    Handler (..),
    op,
    handleWith,
    interpret,
  )
where

import Control.Arrow
import Control.Arrow.Effect (Handler (..))
import Control.Category
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Misc

unit :: (Arrow a) => a b (b, ())
unit = arr (,())

ununit :: (Arrow a) => a (b, ()) b
ununit = arr fst

assoc :: (Arrow a) => a ((b, c), d) (b, (c, d))
assoc = arr \((b, c), d) -> (b, (c, d))

unassoc :: (Arrow a) => a (b, (c, d)) ((b, c), d)
unassoc = arr \(b, (c, d)) -> ((b, c), d)

--------------------------------------------------------------------------------
-- A final-encoded (really?) version of the effectuful arrows

newtype Eff op b c = Eff
  { runEff ::
      forall a d.
      (Arrow a) =>
      (forall i o x. op i o -> a (o, x) d -> a (i, x) d) -> -- effect handler
      (forall x. a (c, x) d -> a (b, x) d)
  }

instance Category (Eff op) where
  id = Eff \_ k -> k
  Eff f . Eff g = Eff \effh k -> g effh (f effh k)

instance Arrow (Eff op) where
  arr f = Eff \_ k -> arr (first f) >>> k
  first (Eff f) = Eff \effh k -> assoc >>> f effh (unassoc >>> k)

op :: op i o -> Eff op i o
op e = Eff \effh k -> effh e k

handleWith ::
  forall op a b c d.
  (Arrow a) =>
  Handler op a c d ->
  Eff op b c ->
  a b d
handleWith Handler {..} (Eff f) = unit >>> f effh (ununit >>> valh)

interpret :: (Arrow a) => (forall i o. op i o -> a i o) -> Eff op b c -> a b c
interpret f =
  handleWith Handler {valh = returnA, effh = \e k -> first (f e) >>> k}
