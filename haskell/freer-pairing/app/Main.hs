{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
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
newtype ObjectF f g a = ObjectF (forall x r. f x -> (x -> a -> g r) -> g r)
  deriving (Functor)

type instance Base (Object f g) = ObjectF f g

instance (Monad g) => Recursive (Object f g) where
  project (Object f) = ObjectF \m k -> f m >>= uncurry k

instance (Monad g) => Corecursive (Object f g) where
  embed (ObjectF f) = Object \m -> f m \x o -> pure (x, o)

-- `ObjectF f Identity` pairs with `Coyoneda f`
coyonedaObjectF :: Pairing (Coyoneda f) (ObjectF f Identity)
coyonedaObjectF f (Coyoneda g m) (ObjectF n) = runIdentity $ n m \x b -> Identity $ f (g x) b

type Freer f = Free (Coyoneda f)

-- `Cofree (ObjectF f Identity)` pairs with `Freer f`
freerCofreeObjectF :: Pairing (Freer f) (Cofree (ObjectF f Identity))
freerCofreeObjectF = freeCofree coyonedaObjectF

send :: f a -> Freer f a
send = liftF . liftCoyoneda

-- Cofree (ObjectF f Identity) (a -> b) can be seen as a shallow handler!
type Handler f a b = Cofree (ObjectF f Identity) (a -> b)

pattern Handler :: (a -> b) -> (forall x r. f x -> (x -> Handler f a b -> r) -> r) -> Handler f a b
pattern Handler {valh, effh} <- valh :< ObjectF (aux -> effh)
  where
    Handler vh eh = vh :< ObjectF eh

runWith :: Handler f a b -> Freer f a -> b
runWith h m = freerCofreeObjectF (&) m h

aux ::
  (forall x r. f x -> (x -> Handler f a b -> Identity r) -> Identity r) ->
  (forall x r. f x -> (x -> Handler f a b -> r) -> r)
aux f m k = runIdentity $ f m \x h -> Identity $ k x h

--------------------------------------------------------------------------------

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
tf = runWith true
  where
    true, false :: Handler Amb a a
    true = Handler {valh = id, effh = \Flip k -> k True false}
    false = Handler {valh = id, effh = \Flip k -> k False true}

main :: IO ()
main = print $ tf $ replicateM 10 (send Flip)
