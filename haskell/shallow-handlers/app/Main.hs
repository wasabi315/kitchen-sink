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

fromNat :: Monad m => (forall x. f x -> m x) -> Cofree (ObjectF f m) ()
fromNat f = coiter (\s -> ObjectF $ fmap (,s) . f) ()

runFreer :: Monad m => Cofree (ObjectF f m) () -> Freer f a -> m a
runFreer (_ :< _) (Pure a) = pure a
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
evalState1 = \m s -> runIdentity $ runFreer (() <$ coiter h s) m
  where
    h :: s -> ObjectF (State s) Identity s
    h s = ObjectF \case
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
