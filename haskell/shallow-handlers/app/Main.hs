{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

import Control.Comonad.Cofree
import Control.Exception
import Control.Monad
import Control.Monad.Free hiding (unfold)
import Control.Monad.State qualified as Mtl
import Control.Object
import Data.Functor.Coyoneda
import Data.Functor.Foldable hiding (unfold)
import Data.Functor.Identity

assertIO :: Bool -> IO ()
assertIO b = assert b pure ()

-- Freer

type Freer f = Free (Coyoneda f)

pattern Bind :: f b -> (b -> Freer f a) -> Freer f a
pattern Bind m k = Free (Coyoneda k m)

{-# COMPLETE Pure, Bind #-}

send :: f a -> Freer f a
send = liftF . liftCoyoneda

-- The base functor of Object

-- newtype ObjectF f g a = ObjectF (forall x. f x -> g (x, a))
newtype ObjectF f g a = ObjectF (forall x r. f x -> (x -> a -> g r) -> g r)
  deriving stock (Functor)

type instance Base (Object f g) = ObjectF f g

instance Monad g => Recursive (Object f g) where
  project (Object f) = ObjectF \m k -> f m >>= uncurry k

instance Monad g => Corecursive (Object f g) where
  embed (ObjectF f) = Object \m -> f m \x obj -> pure (x, obj)

-- Shallow handler defined with Cofree

type SH f m a b = Cofree (ObjectF f m) (a -> m b)

pattern SH ::
  (a -> m b) ->
  (forall x r. f x -> (x -> SH f m a b -> m r) -> m r) ->
  SH f m a b
pattern SH {retc, effc} = retc :< ObjectF effc

{-# COMPLETE SH #-}

unfoldSH ::
  (s -> a -> m b) -> -- state -> value handler
  (forall x r. s -> f x -> (x -> s -> m r) -> m r) -> -- state -> (effect handler x state)
  s ->
  SH f m a b
unfoldSH f g = unfold \s -> (f s, ObjectF (g s))

deep :: (a -> m b) -> (forall x r. f x -> (x -> m r) -> m r) -> SH f m a b
deep retc effc = sh where sh = SH {retc, effc = \m k -> effc m (flip k sh)}

fromNat :: Monad m => (forall x. f x -> m x) -> SH f m a a
fromNat f = deep pure \x -> (f x >>=)

runFreer :: Monad m => SH f m a b -> Freer f a -> m b
runFreer SH {retc} (Pure a) = retc a
runFreer SH {effc} (Bind m k) = effc m \x sh -> runFreer sh (k x)

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
    h :: s -> State s a -> (a -> s -> Identity r) -> Identity r
    h s Get k = k s s
    h _ (Put s) k = k () s

evalState2 :: Freer (State s) a -> s -> a
evalState2 = Mtl.evalState . runFreer (fromNat h)
  where
    h :: State s a -> Mtl.State s a
    h Get = Mtl.get
    h (Put s) = Mtl.put s

testState :: IO ()
testState = do
  let m = do
        a <- get
        b <- get
        put (100 :: Int)
        c <- get
        put b
        d <- get
        pure [a, b, c, d]
      res1 = evalState1 m 0
      res2 = evalState2 m 0
  assertIO $ res1 == res2
  assertIO $ res1 == [0, 0, 100, 0]

-- CoinFlip

data CoinFlip a where
  CoinFlip :: CoinFlip Bool

coinFlip :: Freer CoinFlip Bool
coinFlip = send CoinFlip

alternating :: Freer CoinFlip a -> a
alternating = runIdentity . runFreer t
  where
    t, f :: SH CoinFlip Identity a a
    t = SH {retc = pure, effc = \CoinFlip k -> k True f}
    f = SH {retc = pure, effc = \CoinFlip k -> k False t}

testCoinFlip :: IO ()
testCoinFlip = do
  let m = alternating $ replicateM 10 coinFlip
      n = take 10 $ cycle [True, False]
  assertIO $ m == n

main :: IO ()
main = do
  testState
  testCoinFlip
