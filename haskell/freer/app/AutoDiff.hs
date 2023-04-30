{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoFieldSelectors #-}

module AutoDiff (grad) where

import Control.Applicative (Applicative (liftA2))
import Control.Monad
import Control.Monad.ST
import Data.STRef
import Freer

data V s a = V {v :: !a, d :: STRef s a}

newV :: Num a => a -> ST s (V s a)
newV v = do
  d <- newSTRef 0
  pure V {v, d}

data AutoDiff s a b where
  Val :: a -> AutoDiff s a (V s a)
  Add :: V s a -> V s a -> AutoDiff s a (V s a)
  Mul :: V s a -> V s a -> AutoDiff s a (V s a)

run :: Num a => FreerC (AutoDiff s a) (V s a) -> ST s (V s a)
run =
  flip
    runFreerC
    Handler
      { handlePure = \r -> r <$ writeSTRef r.d 1,
        handleBind = \case
          Val v -> \k -> do
            d <- newSTRef 0
            k V {v, d}
          Add a b -> \k -> do
            d <- newSTRef 0
            let x = V {v = a.v + b.v, d}
            void $ k x
            xd <- readSTRef x.d
            modifySTRef' a.d (+ xd)
            modifySTRef' b.d (+ xd)
            pure x
          Mul a b -> \k -> do
            d <- newSTRef 0
            let x = V {v = a.v + b.v, d}
            void $ k x
            xd <- readSTRef x.d
            modifySTRef' a.d (+ (b.v * xd))
            modifySTRef' b.d (+ (a.v * xd))
            pure x
      }

newtype Expr s a = Expr (FreerC (AutoDiff s a) (V s a))

instance Num a => Num (Expr s a) where
  fromInteger x = Expr do
    sendC $ Val (fromInteger x)

  Expr m + Expr n = Expr do
    sendC =<< liftA2 Add m n

  Expr m * Expr n = Expr do
    sendC =<< liftA2 Mul m n

  abs = error "boom"
  signum = error "boom"
  negate = error "boom"

grad :: Fractional a => (forall s. Expr s a -> Expr s a) -> a -> a
grad f x = runST do
  v <- newV x
  void $ run case f (Expr (pure v)) of Expr m -> m
  readSTRef v.d
