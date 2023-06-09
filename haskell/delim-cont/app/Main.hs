{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

import Control.Monad.Free
import Control.Applicative
import Control.Monad
import GHC.Exts
import GHC.IO

-- Delim cont operations

newtype Mom a = Mom {unMom :: IO a}
  deriving newtype
    ( Functor,
      Applicative,
      Monad,
      Alternative,
      MonadPlus,
      Semigroup,
      Monoid
    )

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: Mom (PromptTag a)
newPromptTag =
  Mom $ IO \s ->
    case newPromptTag# s of
      (# s', tag #) -> (# s', PromptTag tag #)

prompt :: PromptTag a -> Mom a -> Mom a
prompt (PromptTag tag) (Mom (IO m)) = Mom (IO (prompt# tag m))

control0 :: PromptTag a -> ((Mom b -> Mom a) -> Mom a) -> Mom b
control0 (PromptTag tag) f =
  Mom . IO $ control0# tag \k ->
    case f (\(Mom (IO a)) -> Mom (IO (k a))) of
      Mom (IO b) -> b

-- Effects

type f % r = PromptTag (Free (Co f) r)

type Continuation c f a = c -> Mom (Free (Co f) a)

data Co f a where
  Co :: f x -> (x -> Mom a) -> Co f a

perform :: f % r -> f a -> Mom a
perform tag eff = control0 tag \k -> pure . Free $ Co eff (k . pure)

fiber :: (a -> Mom b) -> Continuation a f b
fiber f x = Pure <$> f x

data Handler f a b = Handler
  { retc :: a -> Mom b,
    effc :: forall x. f x -> Continuation x f a -> Mom b
  }

continueWith :: f % a -> Continuation c f a -> c -> Handler f a b -> Mom b
continueWith tag k c Handler {..} = do
  next <- prompt tag (k c)
  case next of
    Pure a -> retc a
    Free (Co eff k') -> effc eff k'

-- State

data State s a where
  Get :: State s s
  Put :: s -> State s ()

get :: State s % r -> Mom s
get tag = perform tag Get

put :: State s % r -> s -> Mom ()
put tag = perform tag . Put

evalState :: forall s a. s -> (State s % a -> Mom a) -> Mom a
evalState = \s0 f -> do
  tag <- newPromptTag
  continueWith tag (fiber f) tag (handler tag s0)
  where
    handler :: State s % a -> s -> Handler (State s) a a
    handler tag s = Handler
      { retc = pure,
        effc = \case
          Get -> \k -> continueWith tag k s (handler tag s)
          Put s' -> \k -> continueWith tag k () (handler tag s')
      }

-- Generator

data Yield e a where
  Yield :: e -> Yield e ()

yield :: Yield e % r -> e -> Mom ()
yield tag = perform tag . Yield

type Gen e = Mom (Maybe e)

data Status e a
  = NotStarted
  | InProgress (Continuation () (Yield e) a)
  | Finished

fromFoldable :: forall f a r. Foldable f => State (Status a ()) % r -> f a -> Mom (Gen a)
fromFoldable stateTag as = gen <$> newPromptTag
  where
    gen tag = do
      s <- get stateTag
      case s of
        Finished -> pure Nothing
        NotStarted -> do
          put stateTag $ InProgress $ fiber \_ -> mapM_ (yield tag) as
          gen tag
        InProgress k -> do
          continueWith tag k () Handler
            { retc = \() ->
                Nothing <$ put stateTag Finished,
              effc = \(Yield e) k' ->
                Just e <$ put stateTag (InProgress k')
            }

-- Echo

data Echo a where
  Echo :: Show a => a -> Echo ()

echo :: Show a => Echo % r -> a -> Mom ()
echo tag = perform tag . Echo

toStdout :: forall a. (Echo % a -> Mom a) -> Mom a
toStdout = \f -> do
  tag <- newPromptTag
  continueWith tag (fiber f) tag (handler tag)
  where
    handler :: Echo % a -> Handler Echo a a
    handler tag = h
      where
        h = Handler
          { retc = pure,
            effc = \(Echo a) k -> do
              Mom $ print a
              continueWith tag k () h
          }

main :: IO ()
main = unMom do
  toStdout \echoTag -> do
    evalState NotStarted \stateTag -> do
      g <- fromFoldable stateTag [1 :: Int .. 10]
      replicateM_ 15 (g >>= echo echoTag)
