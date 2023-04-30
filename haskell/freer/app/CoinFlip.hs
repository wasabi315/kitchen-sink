{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}

module CoinFlip
  ( CoinFlip,
    coinFlip,
    exhaustively,
    randomly,
  )
where

import Control.Monad.IO.Class
import Freer
import System.Random.Stateful

data CoinFlip a where
  CoinFlip :: CoinFlip Bool

coinFlip :: FreerC CoinFlip Bool
coinFlip = sendC CoinFlip

exhaustively :: FreerC CoinFlip a -> [a]
exhaustively = flip runFreerC $
  fromNatTrans \CoinFlip -> [False, True]

randomly :: MonadIO m => FreerC CoinFlip a -> m a
randomly m = liftIO do
  g <- newIOGenM =<< initStdGen
  let h = fromNatTrans \CoinFlip -> uniformM g
  runFreerC m h
