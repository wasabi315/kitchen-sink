{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}

import Control.Comonad (Comonad (..), ComonadApply (..))
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Maybe
import Numeric.Natural

main = pure ()

--------------------------------------------------------------------------------

fix :: (a -> a) -> a
fix f = let x = f x in x

--------------------------------------------------------------------------------

class (Monad m) => MonadFix m where
  mfix :: (a -> m a) -> m a

instance MonadFix Identity where
  mfix f = fix (f . runIdentity)

instance MonadFix ((->) r) where
  mfix f x = fix \u -> f u x

instance MonadFix [] where
  mfix f = case fix (f . head) of
    [] -> []
    (x : _) -> x : mfix (drop 1 . f)

instance MonadFix Maybe where
  mfix f = fix (f . fromJust)

--------------------------------------------------------------------------------

loeb :: (Functor f) => f (f a -> a) -> f a
loeb f = fix \u -> fmap ($ u) f

--------------------------------------------------------------------------------

cfix :: (Comonad w) => (w a -> a) -> w a
cfix f = fix (extend f)

wfix :: (Comonad w) => w (w a -> a) -> a
wfix w = extract w (extend wfix w)

kfix :: (ComonadApply w) => w (w a -> a) -> w a
kfix w = fix \u -> w <@> duplicate u

--------------------------------------------------------------------------------
-- Guarded recursion

-- Supposed to be abstract
newtype Later a = Later a
  deriving (Functor, Applicative) via Identity
  deriving (Show) via a

lfix :: (Later a -> a) -> a
lfix f = fix (f . pure)

class Predictable f where
  predict :: Later (f a) -> f (Later a)

lcfix :: (Comonad w, Predictable w) => (w (Later a) -> a) -> w a
lcfix f = lfix (extend f . predict)

lwfix :: (Comonad w, Predictable w) => w (w (Later a) -> a) -> a
lwfix = lfix \f w -> extract w (predict (flip extend w <$> f))

lkfix :: (ComonadApply w, Predictable w) => w (w (Later a) -> a) -> w a
lkfix w = lfix \u -> w <@> duplicate (predict u)

data Stream a = a :> Later (Stream a)
  deriving (Functor, Show)

infixr 5 :>

fromFun :: (Natural -> a) -> Stream a
fromFun = lfix \f g -> g 0 :> (f <*> pure (g . succ))

srepeat :: a -> Stream a
srepeat x = lfix (x :>)

shead :: Stream a -> a
shead (x :> _) = x

stail :: Stream a -> Later (Stream a)
stail (_ :> s) = s

instance Comonad Stream where
  extract = shead
  duplicate = lfix \d s -> s :> (d <*> stail s)
  extend f = lfix \e s -> f s :> (e <*> stail s)

instance Applicative Stream where
  pure x = lfix (x :>)
  (<*>) = lfix \a fs xs -> (shead fs $ shead xs) :> (a <*> stail fs <*> stail xs)

instance ComonadApply Stream

instance Predictable Stream where
  predict = lfix \p xs -> (shead <$> xs) :> (p <*> (stail <$> xs))

--------------------------------------------------------------------------------

rfix :: (Representable f) => (a -> f a) -> f a
rfix f = tabulate \i -> fix \u -> f u `index` i
