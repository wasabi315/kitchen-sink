{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- Effect handlers for arrows
-- Ref: https://www.kurims.kyoto-u.ac.jp/~tsanada/papers/jssst2023-arrow-handler.pdf

import Control.Arrow
import Control.Category
import Control.Exception (assert)
import Data.Foldable
import Prelude hiding (id, (.))

{-

  λᵒ x. Q         | proc x -> Q
  L ● M           | L -< M
  [M]             | returnA -< M
  let x <= P in Q | do { x <- P; Q }
  op(M)           | Eff op -< M
  handle R with H | (| (handleWith H) R |)

-}

data Eff op b c where
  Arr :: (b -> c) -> Eff op b c
  Op :: op b c -> Eff op b c
  Comp :: Eff op b c -> Eff op c d -> Eff op b d
  First :: Eff op b c -> Eff op (b, d) (c, d)

instance Category (Eff op) where
  id = Arr id
  (.) = flip Comp

instance Arrow (Eff op) where
  arr = Arr
  first = First

data Handler op a c d = Handler
  { valh :: a c d,
    effh :: forall x y s. op x y -> a (y, s) d -> a (x, s) d
  }

interpret :: Arrow a => (forall x y. op x y -> a x y) -> Handler op a b b
interpret f = Handler {valh = returnA, effh = \op k -> first (f op) >>> k}

handleWith :: forall op a b c d. Arrow a => Handler op a c d -> Eff op b c -> a b d
handleWith Handler {..} m = unit >>> go m (unitInv >>> valh)
  where
    go :: forall x y s. Eff op x y -> a (y, s) d -> a (x, s) d
    go (Arr f) k = first (arr f) >>> k
    go (Op eff) k = effh eff k
    go (Comp f g) k = go f $ go g k
    go (First f) k = assoc >>> go f (assocInv >>> k)

unit :: Arrow a => a b (b, ())
unit = arr (,())

unitInv :: Arrow a => a (b, ()) b
unitInv = arr fst

assoc :: Arrow a => a ((b, c), d) (b, (c, d))
assoc = arr \((a, b), c) -> (a, (b, c))

assocInv :: Arrow a => a (b, (c, d)) ((b, c), d)
assocInv = arr \(a, (b, c)) -> ((a, b), c)

-- Example

data Ops b c where
  F :: Ops Int Int

hSucc :: Arrow a => Handler Ops a b b
hSucc = interpret \case
  F -> arr succ

hResX10 :: Arrow a => Handler Ops a Int Int
hResX10 =
  Handler
    { valh = returnA,
      effh = \case
        F -> \k -> k >>> arr (* 10)
    }

hNondet :: ArrowPlus a => Handler Ops a b b
hNondet = interpret \case
  F -> proc n -> (returnA -< n) <+> (returnA -< n + 1)

test :: Eff Ops Int Int
test = proc n -> do
  m <- Op F -< n
  o <- Op F -< n + m
  returnA -< o

test2 :: Arrow a => Handler Ops a Int Int -> a Int Int
test2 h = proc n -> do
  r <- (| (handleWith h) (do test -< n) |)
  returnA -< r + n

main :: IO ()
main = do
  for_ [0 .. 10] \n -> do
    assertIO do
      handleWith hSucc test n == 2 * n + 2
    assertIO do
      handleWith hResX10 test n == 200 * n
    assertIO do
      runKleisli (handleWith hNondet test) n == [2 * n, 2 * n + 1, 2 * n + 1, 2 * n + 2]
    assertIO do
      runKleisli (test2 hNondet) n == Just (2 * n + n)

  putStrLn "OK"

assertIO :: Bool -> IO ()
assertIO = flip assert (pure ())
