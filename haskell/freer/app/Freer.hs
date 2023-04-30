{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Freer
  ( Freer (..),
    send,
    Handler (..),
    fromNatTrans,
    runFreer,
    FreerF (..),
    runFreer',
    FreerC (..),
    sendC,
  )
where

import Control.Monad
import Data.Functor.Foldable

-- Freer monad and handler

data Freer f a where
  Pure :: a -> Freer f a
  Bind :: f x -> (x -> Freer f a) -> Freer f a

send :: f a -> Freer f a
send m = Bind m Pure

instance Functor (Freer f) where
  fmap f (Pure a) = Pure $ f a
  fmap f (Bind m k) = Bind m $ fmap f . k

instance Applicative (Freer f) where
  pure = Pure

  Pure f <*> m = fmap f m
  Bind m k <*> n = Bind m $ (<*> n) . k

instance Monad (Freer f) where
  Pure a >>= k = k a
  Bind m k >>= k' = Bind m $ k' <=< k

data Handler f a b = Handler
  { handlePure :: a -> b,
    handleBind :: forall x. f x -> (x -> b) -> b
  }

fromNatTrans :: Monad m => (forall x. f x -> m x) -> Handler f a (m a)
fromNatTrans nat =
  Handler
    { handlePure = pure,
      handleBind = \m k -> nat m >>= k
    }

runFreer :: Handler f a b -> Freer f a -> b
runFreer h (Pure a) = handlePure h a
runFreer h (Bind m k) = handleBind h m $ runFreer h . k

-- The connection to recursion-schemes

data FreerF f a y where
  PureF :: a -> FreerF f a y
  BindF :: f x -> (x -> y) -> FreerF f a y

deriving instance Functor (FreerF f a)

type instance Base (Freer f a) = FreerF f a

instance Recursive (Freer f a) where
  project (Pure a) = PureF a
  project (Bind m k) = BindF m k

instance Corecursive (Freer f a) where
  embed (PureF a) = Pure a
  embed (BindF m k) = Bind m k

-- just a catamorphism
runFreer' :: Handler f a b -> Freer f a -> b
runFreer' h = cata \case
  PureF a -> handlePure h a
  BindF m k -> handleBind h m k

-- Church-encoded version

newtype FreerC f a = FreerC
  { runFreerC :: forall r. Handler f a r -> r
  }

sendC :: f a -> FreerC f a
sendC m = FreerC \h -> handleBind h m $ handlePure h

instance Functor (FreerC f) where
  fmap f (FreerC k) = FreerC \h ->
    k h {handlePure = handlePure h . f}

instance Applicative (FreerC f) where
  pure a = FreerC \h -> handlePure h a

  FreerC k <*> m = FreerC \h ->
    k h {handlePure = \f -> runFreerC m h {handlePure = handlePure h . f}}

instance Monad (FreerC f) where
  FreerC k >>= k' = FreerC \h ->
    k h {handlePure = \a -> runFreerC (k' a) h}
