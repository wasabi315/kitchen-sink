{-# LANGUAGE BlockArguments #-}

import Control.Applicative
import Control.Comonad
import Control.Monad
import Data.Foldable

--------------------------------------------------------------------------------

-- Cofreer f ~ Cofree (Yoneda f)
data Cofreer f a = Cofreer a (forall x. (Cofreer f a -> x) -> f x)

-- No Functor constraint on f!
unfold :: (s -> a) -> (forall x. s -> (s -> x) -> f x) -> s -> Cofreer f a
unfold f g s = Cofreer (f s) \k -> g s (k . unfold f g)

unfold' :: (Functor f) => (s -> a) -> (s -> f s) -> s -> Cofreer f a
unfold' f g = unfold f \s k -> k <$> g s

section :: (Comonad w) => w a -> Cofreer w a
section = unfold extract (=>>)

--------------------------------------------------------------------------------

-- No Functor constraint on f!
deriving instance Functor (Cofreer f)

-- No Functor constraint on f!
instance Comonad (Cofreer f) where
  extract (Cofreer a _) = a
  duplicate w@(Cofreer _ f) = Cofreer w \k -> f (k . duplicate)
  extend f w@(Cofreer _ g) = Cofreer (f w) \k -> g (k . extend f)

instance (Alternative f) => Applicative (Cofreer f) where
  pure a = Cofreer a (const empty)
  (<*>) = ap

instance (Alternative f) => Monad (Cofreer f) where
  Cofreer a f >>= k = case k a of
    Cofreer b g -> Cofreer b \l -> g l <|> f (l . (>>= k))

instance (Foldable f) => Foldable (Cofreer f) where
  foldMap f (Cofreer a g) = f a <> fold (g (foldMap f))

instance (Traversable f) => Traversable (Cofreer f) where
  traverse f (Cofreer a g) =
    (\a' w -> Cofreer a' (<$> w))
      <$> f a
      <*> traverse (traverse f) (g id)

--------------------------------------------------------------------------------

-- Any applications?
