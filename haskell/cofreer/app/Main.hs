{-# LANGUAGE BlockArguments #-}

import Control.Comonad

--------------------------------------------------------------------------------

-- Cofreer f ~ Cofree (Yoneda f)
data Cofreer f a = Cofreer a (forall x. (Cofreer f a -> x) -> f x)
  deriving (Functor)

-- No Functor constraint on f!
instance Comonad (Cofreer f) where
  extract (Cofreer a _) = a
  duplicate w@(Cofreer _ f) = Cofreer w \k -> f (k . duplicate)
  extend f w@(Cofreer _ g) = Cofreer (f w) \k -> g (k . extend f)

-- No Functor constraint on f!
unfold :: (s -> a) -> (forall x. s -> (s -> x) -> f x) -> s -> Cofreer f a
unfold f g s = Cofreer (f s) \k -> g s (k . unfold f g)

unfold' :: (Functor f) => (s -> a) -> (s -> f s) -> s -> Cofreer f a
unfold' f g = unfold f \s k -> k <$> g s

section :: (Comonad w) => w a -> Cofreer w a
section = unfold extract (=>>)
