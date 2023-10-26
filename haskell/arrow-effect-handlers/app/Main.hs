{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    effh :: forall x y e. eff x y -> k (y, e) c -> k (x, e) c
  }

interpret :: Arrow k => (forall x y. eff x y -> k x y) -> Handler eff k a a
interpret f = Handler {valh = returnA, effh = \eff k -> first (f eff) >>> k}

runFree :: forall eff k a b c. Arrow k => Handler eff k b c -> Free eff a b -> k a c
runFree Handler {..} m = arr unit >>> go m (arr deunit >>> valh)
  where
    go :: Free eff x y -> k (y, e) c -> k (x, e) c
    go (Arr f) k = first (arr f) >>> k
    go (Eff eff) k = effh eff k
    go (Comp f g) k = go f $ go g k
    go (First f) k = arr assoc >>> go f (arr unassoc >>> k)

unit :: a -> (a, ())
unit a = (a, ())

deunit :: (a, ()) -> a
deunit (a, ()) = a

assoc :: ((a, b), c) -> (a, (b, c))
assoc ((a, b), c) = (a, (b, c))

unassoc :: (a, (b, c)) -> ((a, b), c)
unassoc (a, (b, c)) = ((a, b), c)

-- Example

data Gate a b where
  Gate :: Gate Int Int

hSucc :: Arrow k => Handler Gate k a a
hSucc = interpret \Gate -> arr succ

hResX10 :: Arrow k => Handler Gate k Int Int
hResX10 = Handler {valh = returnA, effh = \Gate k -> k >>> arr (* 10)}

hNondet :: ArrowPlus k => Handler Gate k a a
hNondet = interpret \Gate -> proc n -> (returnA -< n) <+> (returnA -< n + 1)

test :: Free Gate Int Int
test = proc n -> do
  m <- Eff Gate -< n
  o <- Eff Gate -< n + m
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
