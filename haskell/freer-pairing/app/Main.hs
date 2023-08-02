{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

import Control.Comonad.Cofree
import Control.Monad
import Control.Monad.Free
import Control.Object
import Data.Function
import Data.Functor.Coyoneda
import Data.Functor.Foldable
import Data.Functor.Identity

-- Pairing

type Pairing f g = forall a b c. (a -> b -> c) -> f a -> g b -> c

freeCofree :: Pairing f g -> Pairing (Free f) (Cofree g)
freeCofree _ f (Pure a) (b :< _) = f a b
freeCofree p f (Free m) (_ :< w) = p (freeCofree p f) m w

-- The base functor of Object
newtype ObjectF f g a = ObjectF (forall x. f x -> g (x, a))
  deriving (Functor)

type instance Base (Object f g) = ObjectF f g

instance Functor g => Recursive (Object f g) where
  project (Object f) = ObjectF f

instance Functor g => Corecursive (Object f g) where
  embed (ObjectF f) = Object f

-- `ObjectF f Identity` pairs with `Coyoneda f`?
coyonedaObjectF :: Pairing (Coyoneda f) (ObjectF f Identity)
coyonedaObjectF f (Coyoneda g m) (ObjectF n) = let Identity (x, b) = n m in f (g x) b

type Freer f = Free (Coyoneda f)

-- `Cofree (ObjectF f Identity)` pairs with `Freer f` then?
freerCofreeObjectF :: Pairing (Freer f) (Cofree (ObjectF f Identity))
freerCofreeObjectF = freeCofree coyonedaObjectF

send :: f a -> Freer f a
send = liftF . liftCoyoneda

-- Cofree (ObjectF f Identity) can be seen as a state machine whose states correspond to handlers

type Handlers f a b = Cofree (ObjectF f Identity) (a -> b)

pattern Handlers :: (a -> b) -> (forall x. f x -> Identity (x, Handlers f a b)) -> Handlers f a b
pattern Handlers {valh, effh} = valh :< ObjectF effh

data Amb a where
  Flip :: Amb Bool

{-
      +----+ Amb  +-----+
      |    | ---> |     |
  --> |true|      |false|
      |    | <--- |     |
      +----+  Amb +-----+
-}
tf :: forall a. Freer Amb a -> a
tf m = freerCofreeObjectF (&) m true
  where
    true, false :: Handlers Amb a a
    true = Handlers {valh = id, effh = \Flip -> pure (True, false)}
    false = Handlers {valh = id, effh = \Flip -> pure (False, true)}

main :: IO ()
main = print $ tf $ replicateM 10 (send Flip)
