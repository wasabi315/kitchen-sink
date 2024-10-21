{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}

module Main where

import Control.Arrow.Effect
import Control.Arrow.Effect.Nondet
import Control.Arrow.Effect.Reader
import Control.Arrow.Effect.State

main :: IO ()
main = do
  print $ testReader ((), 10)
  print $ testState (100, 1)
  print $ testNondet 1

--------------------------------------------------------------------------------

-- |
-- prop> testReader ((), n) == 2 * n + 1
testReader :: ((), Int) -> Int
testReader = runReader proc () -> do
  r <- ask -< ()
  r' <- local (+ 1) ask -< ()
  returnA -< r + r'

-- |
-- prop> testState (n, s) == (s, n + s)
testState :: (Int, Int) -> (Int, Int)
testState = runState proc n -> do
  s <- get -< ()
  put -< n + s
  returnA -< s

-- |
-- prop> testNondet n == [n, n + 1]
testNondet :: Int -> [Int]
testNondet = runKleisli $ runNonDet proc n ->
  do returnA -< n
    <+> do returnA -< n + 1
