{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Arrow
import Control.Arrow.Effect
import Control.Arrow.Effect.ArrowApply qualified as ArrowApply
import Control.Arrow.Effect.Final qualified as Final
import Control.Arrow.Effect.MoreInputs qualified as MoreInputs
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------

data SuccRes i o where
  SuccRes :: SuccRes x x

runSuccRes :: (Arrow a) => Eff SuccRes b Int -> a b Int
runSuccRes =
  handleWith
    Handler
      { valh = returnA,
        effh = \SuccRes k -> k >>> arr succ
      }

runSuccResC :: (Arrow a) => Final.Eff SuccRes b Int -> a b Int
runSuccResC =
  Final.handleWith
    Handler
      { valh = returnA,
        effh = \SuccRes k -> k >>> arr succ
      }

runSuccResAA :: (ArrowApply a) => ArrowApply.Eff SuccRes b Int -> a b Int
runSuccResAA =
  ArrowApply.handleWith
    ArrowApply.Handler
      { valh = returnA,
        effh = \SuccRes k -> k >>> arr succ
      }

testSuccRes :: Int -> Int
testSuccRes = runSuccRes proc n -> do
  m <- Op SuccRes -< 2 * n
  o <- Op SuccRes -< m
  returnA -< m + o

testSuccResF :: Int -> Int
testSuccResF = runSuccResC proc n -> do
  m <- Final.op SuccRes -< 2 * n
  o <- Final.op SuccRes -< m
  returnA -< m + o

testSuccResAA :: Int -> Int
testSuccResAA = runSuccResAA proc n -> do
  m <- Op SuccRes -< 2 * n
  o <- Op SuccRes -< m
  returnA -< m + o

--------------------------------------------------------------------------------

data Amb i o where
  Flip :: Amb () Bool

runAmb :: (ArrowPlus a) => Eff Amb b c -> a b c
runAmb = interpret \Flip -> arr (const True) <+> arr (const False)

testAmb :: Int -> [Int]
testAmb = runKleisli $ runAmb proc n -> do
  b1 <- Op Flip -< ()
  b2 <- Op Flip -< ()
  returnA -< if b1 || b2 then n else -n

--------------------------------------------------------------------------------

data State s i o where
  Get :: State s () s
  Set :: State s s ()

runState :: forall a s b c. (Arrow a) => Eff (State s) b c -> a (b, s) (c, s)
runState m = proc (b, s) -> (| (MoreInputs.handleWith h) (m -< b) |) s
  where
    h :: MoreInputs.Handler (State s) a s c (c, s)
    h =
      MoreInputs.Handler
        { valh = returnA,
          effh = \cases
            Get k -> proc ((), s, x) -> k -< (s, s, x)
            Set k -> proc (s, _, x) -> k -< ((), s, x)
        }

testState :: (Int, Int) -> (Int, Int)
testState = runState proc n -> do
  s <- Op Get -< ()
  Op Set -< n + s
  returnA -< s

--------------------------------------------------------------------------------

main :: IO ()
main = do
  print $ testSuccRes 10
  print $ testSuccResF 10
  print $ testSuccResAA 10
  print $ testAmb 10
  print $ testState (2, 40)
