# Emulate Koka's with syntax using QualifiedDo

```haskell
{-# LANGUAGE QualifiedDo #-}

module Main where

import Data.Foldable

with :: a -> a
with = id

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
  --     for_ [False, True] $ \p ->
  --       for_ [False, True] $ \q ->
  --         print (p, q)
  with twice
  p <- with for_ [False, True]
  q <- with for_ [False, True]
  print (p, q)
```
