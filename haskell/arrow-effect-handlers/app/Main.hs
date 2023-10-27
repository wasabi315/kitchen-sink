{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- Arrow with effect handlers
-- Ref: https://www.kurims.kyoto-u.ac.jp/~tsanada/papers/jssst2023-arrow-handler.pdf

import Control.Arrow
import Control.Category
import Control.Exception (assert)
import Data.Foldable
import Prelude hiding (id, (.))

{-

  \o x. Q         | proc x -> Q
  L o M           | L -< M
  [M]             | returnA -< M
  let x <= P in Q | do { x <- P; Q }
  op(M)           | Eff op -< M
  handle R with H | ???

-}

data Free eff a b where
  Arr :: (a -> b) -> Free eff a b
  Eff :: eff a b -> Free eff a b
  Comp :: Free eff a b -> Free eff b c -> Free eff a c
  First :: Free eff a b -> Free eff (a, c) (b, c)

instance Category (Free eff) where
  id = Arr id
  (.) = flip Comp

instance Arrow (Free eff) where
  arr = Arr
  first = First

data Handler eff k b c = Handler
  { valh :: k b c,
    effh :: forall x y s. eff x y -> k (y, s) c -> k (x, s) c
  }

interpret :: Arrow k => (forall x y. eff x y -> k x y) -> Handler eff k a a
interpret f = Handler {valh = returnA, effh = \eff k -> first (f eff) >>> k}

runFree :: forall eff k a b c. Arrow k => Handler eff k b c -> Free eff a b -> k a c
runFree Handler {..} m = unit >>> go m (unitInv >>> valh)
  where
    go :: forall x y s. Free eff x y -> k (y, s) c -> k (x, s) c
    go (Arr f) k = first (arr f) >>> k
    go (Eff eff) k = effh eff k
    go (Comp f g) k = go f $ go g k
    go (First f) k = assoc >>> go f (assocInv >>> k)

unit :: Arrow k => k a (a, ())
unit = arr (,())

unitInv :: Arrow k => k (a, ()) a
unitInv = arr fst

assoc :: Arrow k => k ((a, b), c) (a, (b, c))
assoc = arr \((a, b), c) -> (a, (b, c))

assocInv :: Arrow k => k (a, (b, c)) ((a, b), c)
assocInv = arr \(a, (b, c)) -> ((a, b), c)

-- Example

data Ops a b where
  F :: Ops Int Int

hSucc :: Arrow k => Handler Ops k a a
hSucc = interpret \case
  F -> arr succ

hResX10 :: Arrow k => Handler Ops k Int Int
hResX10 =
  Handler
    { valh = returnA,
      effh = \case
        F -> \k -> k >>> arr (* 10)
    }

hNondet :: ArrowPlus k => Handler Ops k a a
hNondet = interpret \case
  F -> proc n -> (returnA -< n) <+> (returnA -< n + 1)

test :: Free Ops Int Int
test = proc n -> do
  m <- Eff F -< n
  o <- Eff F -< n + m
  returnA -< o

main :: IO ()
main = do
  for_ [0 .. 10] \n -> do
    assertIO do
      runFree hSucc test n == 2 * n + 2
    assertIO do
      runFree hResX10 test n == 200 * n
    assertIO do
      runKleisli (runFree hNondet test) n == Just (2 * n)
    assertIO do
      runKleisli (runFree hNondet test) n == [2 * n, 2 * n + 1, 2 * n + 1, 2 * n + 2]

  putStrLn "OK"

assertIO :: Bool -> IO ()
assertIO = flip assert (pure ())
