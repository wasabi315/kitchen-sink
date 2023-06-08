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
import Control.Monad.Free hiding (unfold)
import Control.Monad.State qualified as Mtl
import Control.Object
import Data.Functor.Coyoneda
import Data.Functor.Foldable hiding (unfold)
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

type ShallowHandlers f m a b = Cofree (ObjectF f m) (a -> m b)

unfoldSH ::
  Monad m =>
  (s -> a -> m b) -> -- state -> value handler
  (forall x. s -> f x -> m (x, s)) -> -- state -> (effect handler x state)
  s ->
  ShallowHandlers f m a b
unfoldSH f g = unfold \s -> (f s, ObjectF (g s))

fromNat :: Monad m => (forall x. f x -> m x) -> ShallowHandlers f m a a
fromNat f = unfoldSH (const pure) (const $ fmap (,()) . f) ()

runFreer :: Monad m => ShallowHandlers f m a b -> Freer f a -> m b
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
