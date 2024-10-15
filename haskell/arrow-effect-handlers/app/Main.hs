{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Arrow.Effect
import Control.Arrow.Effect.Nondet
import Control.Arrow.Effect.Reader
import Control.Arrow.Effect.State

main :: IO ()
main = do
  print $ testReader (10, ())
  print $ testState (1, 100)
  print $ testNondet 1

--------------------------------------------------------------------------------

testReader :: (Int, ()) -> Int
testReader = runReader proc () -> do
  r <- ask -< ()
  r' <- local (+ 1) ask -< ()
  returnA -< r + r'

testState :: (Int, Int) -> (Int, Int)
testState = runState proc n -> do
  s <- get -< ()
  put -< n + s
  returnA -< s

testNondet :: Int -> [Int]
testNondet = runKleisli $ runNonDet proc n ->
  do returnA -< n
    <+> do returnA -< n + 1
