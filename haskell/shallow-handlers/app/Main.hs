{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

import Control.Comonad.Cofree
import Control.Exception
import Control.Monad.Free
import Control.Monad.State qualified as Mtl
import Control.Object
import Data.Functor.Coyoneda
import Data.Functor.Foldable
import Data.Functor.Identity

-- Freer

type Freer f = Free (Coyoneda f)

send :: f a -> Freer f a
send = liftF . liftCoyoneda

-- The base functor of Object

newtype ObjectF f g a = ObjectF (forall x. f x -> g (x, a))
  deriving stock (Functor)

type instance Base (Object f g) = ObjectF f g

instance Functor g => Recursive (Object f g) where
  project (Object f) = ObjectF f

instance Functor g => Corecursive (Object f g) where
  embed (ObjectF f) = Object f

-- Shallow handler defined with Cofree

type ShallowHandlers f m a = Cofree (ObjectF f m) (a -> m a)

fromNat :: Monad m => (forall x. f x -> m x) -> ShallowHandlers f m a
fromNat f = pure <$ coiter (\() -> ObjectF $ fmap (,()) . f) ()

unfoldSH ::
  Monad m =>
  (s -> a -> m a) -> -- state -> value handler
  (forall x. s -> f x -> m (x, s)) -> -- state -> effect handler
  s ->
  ShallowHandlers f m a
unfoldSH f g s = f s :< (unfoldSH f g <$> ObjectF (g s))

runFreer :: Monad m => ShallowHandlers f m a -> Freer f a -> m a
runFreer (retc :< _) (Pure a) = retc a
runFreer (_ :< ObjectF f) (Free (Coyoneda k m)) = do
  (b, effcs) <- f m
  runFreer effcs (k b)

-- State

data State s a where
  Get :: State s s
  Put :: s -> State s ()

get :: Freer (State a) a
get = send Get

put :: a -> Freer (State a) ()
put = send . Put

evalState1 :: Freer (State s) a -> s -> a
evalState1 = \m s -> runIdentity $ runFreer (unfoldSH (const pure) h s) m
  where
    h :: s -> State s a -> Identity (a, s)
    h s = \case
      Get -> pure (s, s)
      Put s' -> pure ((), s')

evalState2 :: Freer (State s) a -> s -> a
evalState2 = Mtl.evalState . runFreer (fromNat h)
  where
    h :: State s a -> Mtl.State s a
    h = \case
      Get -> Mtl.get
      Put s' -> Mtl.put s'

test :: Freer (State Int) [Int]
test = do
  a <- get
  b <- get
  put 100
  c <- get
  put b
  d <- get
  pure [a, b, c, d]

main :: IO ()
main = assert (evalState1 test 0 == evalState2 test 0) pure ()
