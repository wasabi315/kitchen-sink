{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

import Control.Comonad.Cofree
import Control.Monad.Free
import Data.Bifunctor
import Data.Functor.Coyoneda
import Data.Profunctor

-- Freer

type Freer f = Free (Coyoneda f)

send :: f a -> Freer f a
send = liftF . liftCoyoneda

-- Pairing

type f `Pairing` g = forall a b c. (a -> b -> c) -> f a -> g b -> c

infix 4 `Pairing`

zap :: f `Pairing` g -> f (x -> y) -> g x -> y
zap pairing = pairing ($)

sym :: f `Pairing` g -> g `Pairing` f
sym pairing f m n = pairing (flip f) n m

freeCofree :: f `Pairing` g -> Free f `Pairing` Cofree g
freeCofree _ f (Pure a) (b :< _) = f a b
freeCofree pairing f (Free m) (_ :< w) = pairing (freeCofree pairing f) m w

-- What is this??
newtype Wtf f a = Wtf (forall x. f x -> (x, a))
  deriving stock (Functor)

coyonedaWtf :: Coyoneda f `Pairing` Wtf f
coyonedaWtf f (Coyoneda k m) (Wtf g) = uncurry f . first k $ g m

type Cofreer f = Cofree (Wtf f)

freerCofreer :: Freer f `Pairing` Cofreer f
freerCofreer = freeCofree coyonedaWtf

-- State

data State s a where
  Get :: State s s
  Put :: s -> State s ()

get :: Freer (State a) a
get = send Get

put :: a -> Freer (State a) ()
put = send . Put

handleState :: s -> Wtf (State s) s
handleState s = Wtf \case
  Get -> (s, s)
  Put s' -> ((), s')

evalState :: Freer (State s) a -> s -> a
evalState m s = zap (sym freerCofreer) (id <$ coiter handleState s) m

test :: Freer (State Int) [Int]
test = do
  a <- get
  b <- get
  put 100
  c <- get
  put b
  d <- get
  pure [a, b, c, d]

main :: IO ()
main = print $ evalState test 0

-- Is below true?
-- Deep Handler - Church encoding
-- Shallow Handler - Scott encoding

-- Shallow Handler

data ShallowHandler f a r = ShallowHandler
  { retc :: a -> r,
    effc :: forall x. f x -> (x -> Freer f a) -> r
  }
  deriving stock (Functor)

instance Profunctor (ShallowHandler f) where
  dimap f g ShallowHandler {..} =
    ShallowHandler
      { retc = g . retc . f,
        effc = \m k -> g $ effc m (fmap f . k)
      }

continueWith :: (c -> Freer f a) -> c -> ShallowHandler f a b -> b
continueWith k c ShallowHandler {..} =
  case k c of
    Pure a -> retc a
    Free (Coyoneda k' m) -> effc m k'

startWith :: Freer f a -> ShallowHandler f a b -> b
startWith m = continueWith (const m) ()

monadic :: Monad m => (forall x. f x -> m x) -> ShallowHandler f a (m a)
monadic f = h
  where
    h =
      ShallowHandler
        { retc = pure,
          effc = \eff k -> f eff >>= \x -> continueWith k x h
        }
