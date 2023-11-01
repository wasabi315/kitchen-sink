{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Effect handlers for arrows
-- Ref: https://www.kurims.kyoto-u.ac.jp/~tsanada/papers/jssst2023-arrow-handler.pdf

import Control.Arrow
import Control.Category
import Control.Exception (assert)
import Prelude hiding (id, (.))

{-

  λᵒ x. Q         | proc x -> Q
  L ● M           | L -< M
  [M]             | returnA -< M
  let x <= P in Q | do { x <- P; Q }
  op(M)           | Eff op -< M
  handle R with H | (| (handleWith H) R |) <additional input>

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

data Handler op a e' r r' = Handler
  { valh :: a (e', r) r',
    effh :: forall i o x. op i o -> a (o, e', x) r' -> a (i, e', x) r'
  }

interpret :: (Arrow a) => (forall i o. op i o -> a i o) -> Handler op a () b b
interpret f =
  Handler
    { valh = arr snd,
      effh = \op k -> proc (x, b', z) -> do
        y <- f op -< x
        k -< (y, b', z)
    }

handleWith ::
  forall op a e s e' r r'.
  (Arrow a) =>
  Handler op a e' r r' ->
  Eff op (e, s) r ->
  a (e, (e', s)) r'
handleWith Handler {..} m = proc (e, (e', s)) -> do
  go m (proc (r, e', ()) -> valh -< (e', r)) -< ((e, s), e', ())
  where
    go :: forall i o x. Eff op i o -> a (o, e', x) r' -> a (i, e', x) r'
    go (Arr f) k = proc (i, e', x) -> k -< (f i, e', x)
    go (Op op) k = effh op k
    go (Comp f g) k = go f $ go g k
    go (First f) k = proc ((i, x'), e', x) ->
      go f (proc (o, e', (x', x)) -> k -< ((o, x'), e', x)) -< (i, e', (x', x))

-- Example

data SuccPred b c where
  Succ :: SuccPred Int Int
  Pred :: SuccPred Int Int

runSucc :: (Arrow a) => Eff SuccPred b c -> a b c
runSucc m = proc b -> (| (handleWith h) (m -< b) |) ()
  where
    h = interpret \case
      Succ -> arr succ
      Pred -> arr pred

testSucc :: (Arrow a) => a Int Int
testSucc = runSucc proc n -> do
  m <- Op Succ -< n
  o <- Op Pred -< n
  returnA -< m + o

data State s b c where
  Get :: State s b s
  Set :: State s s ()

runState :: forall a s b c. (Arrow a) => Eff (State s) b c -> a (s, b) (s, c)
runState m = proc (s, a) -> (| (handleWith h) (m -< a) |) s
  where
    h :: Handler (State s) a s r (s, r)
    h =
      Handler
        { valh = returnA,
          effh = \cases
            Get k -> proc (_, s, x) -> k -< (s, s, x)
            Set k -> proc (s', _, x) -> k -< ((), s', x)
        }

testState :: (Arrow a) => a (Int, Int) (Int, Int)
testState = runState proc n -> do
  s <- Op Get -< ()
  Op Set -< n + s
  returnA -< s

main :: IO ()
main = do
  assertIO $ testSucc 10 == 20
  assertIO $ testState (10, 20) == (30, 10)
  putStrLn "OK"

assertIO :: Bool -> IO ()
assertIO = flip assert (pure ())
