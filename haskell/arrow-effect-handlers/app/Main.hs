{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Arrow with effect handlers
-- Ref: https://www.kurims.kyoto-u.ac.jp/~tsanada/papers/jssst2023-arrow-handler.pdf

import Control.Arrow
import Control.Category
import Control.Exception (assert)
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

-- Deep handler
data Handler eff k b c = Handler
  { valh :: k b c,
    effh :: forall x y. eff x y -> k y c -> k x c
  }

interpret :: Arrow k => (forall x y. eff x y -> k x y) -> Handler eff k a a
interpret f = Handler {valh = returnA, effh = \eff k -> f eff >>> k}

-- Can we relax the constraint ArrowApply to Arrow?
runFree :: forall eff k a b c. ArrowApply k => Handler eff k b c -> Free eff a b -> k a c
runFree Handler {..} c = go c valh
  where
    go :: Free eff x y -> k y c -> k x c
    go (Arr f) k = arr f >>> k
    go (Eff eff) k = effh eff k
    go (Comp f g) k = go f $ go g k
    go (First f) k = proc (v, u) -> go f (proc w -> k -< (w, u)) -<< v

-- Example

data Get a b where
  Get :: Get () Bool

hTrue :: Arrow k => Handler Get k a a
hTrue = interpret \Get -> arr (const True)

hFalseNot :: Arrow k => Handler Get k Bool Bool
hFalseNot =
  Handler
    { valh = returnA,
      effh = \Get k -> proc () -> do
        x <- k -< False
        returnA -< not x
    }

hNondet :: ArrowPlus k => Handler Get k a a
hNondet = interpret \Get -> proc () -> (returnA -< False) <+> (returnA -< True)

main :: IO ()
main = do
  let test = proc () -> do
        x <- Eff Get -< ()
        y <- Eff Get -< ()
        z <- Eff Get -< ()
        returnA -< x && y && z

  assertIO do
    runFree hTrue test () == True
  assertIO do
    runFree hFalseNot test () == True
  assertIO do
    runKleisli (runFree hNondet test) () == Just False
  assertIO do
    runKleisli (runFree hNondet test) () == [False, False, False, False, False, False, False, True]

  putStrLn "OK"

assertIO :: Bool -> IO ()
assertIO = flip assert (pure ())
