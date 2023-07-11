{-# LANGUAGE QualifiedDo #-}

module Main where

import Data.Foldable

-- Emulate Koka's with syntax

(>>=) :: ((a -> b) -> c) -> (a -> b) -> c
(>>=) = ($)

(>>) :: (a -> c) -> a -> c
(>>) = ($)

twice :: Applicative f => f () -> f ()
twice m = m *> m

main :: IO ()
main = Main.do
  -- desugared to:
  --   twice $
  --     for_ [False, True] $ \n ->
  --       for_ [False, True] $ \m ->
  --         print (n, m)
  twice
  n <- for_ [False, True]
  m <- for_ [False, True]
  print (n, m)
