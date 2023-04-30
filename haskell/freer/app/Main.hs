{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}

import AutoDiff
import CoinFlip
import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Bits
import Data.Foldable

testAmb :: IO ()
testAmb = do
  let m = liftA2 xor coinFlip coinFlip

  let !_ = assert (exhaustively m == [False, True, True, False]) ()
  putStrLn "OK"

  res <- replicateM 8 $ randomly m
  print res

testAutoDiff :: IO ()
testAutoDiff = do
  let f x = x + x * x * x
      f' x = 1 + 3 * x * x

  for_ [0 :: Int .. 15] \i -> do
    let x = fromIntegral i :: Double
    let !_ =  assert (grad f x == f' x) ()
    pure ()

  putStrLn "OK"

main :: IO ()
main = do
  testAmb
  testAutoDiff
