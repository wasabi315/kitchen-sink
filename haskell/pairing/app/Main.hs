{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

import Control.Comonad.Cofree
import Control.Comonad.Env
import Control.Comonad.Store
import Control.Comonad.Traced (TracedT (..))
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer (WriterT (..))
import Data.Functor.Coyoneda
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum

-- Pairing (ref: https://pursuit.purescript.org/packages/purescript-pairing/5.1.0/docs/Data.Functor.Pairing)

type Pairing f g = forall a b c. (a -> b -> c) -> f a -> g b -> c

zap :: Pairing f g -> f (a -> b) -> g a -> b
zap p = p ($)

sym :: Pairing f g -> Pairing g f
sym p f x y = p (flip f) y x

identity :: Pairing Identity Identity
identity f (Identity a) (Identity b) = f a b

productSum :: Pairing f g -> Pairing f' g' -> Pairing (Product f f') (Sum g g')
productSum p _ f (Pair x _) (InL y) = p f x y
productSum _ p f (Pair _ x) (InR y) = p f x y

stateStore :: Pairing f g -> Pairing (StateT s f) (StoreT s g)
stateStore p f (StateT g) (StoreT w s) = p (\(a, s') sb -> f a (sb s')) (g s) w

readerEnv :: Pairing f g -> Pairing (ReaderT e f) (EnvT e g)
readerEnv p f (ReaderT g) (EnvT e w) = p f (g e) w

writerTraced :: Pairing f g -> Pairing (WriterT m f) (TracedT m g)
writerTraced p f (WriterT x) (TracedT y) = p (\(a, m) mb -> f a (mb m)) x y

freeCofree :: Pairing f g -> Pairing (Free f) (Cofree g)
freeCofree _ f (Pure a) (b :< _) = f a b
freeCofree p f (Free m) (_ :< w) = p (freeCofree p f) m w

-- What's this?
newtype Wtf f a = Wtf (forall x. f x -> (x, a))

instance Functor (Wtf f) where
  fmap f (Wtf n) = Wtf (fmap f . n)

-- `Wtf f` pairs with `Coyoneda f`?
coyonedaWtf :: Pairing (Coyoneda f) (Wtf f)
coyonedaWtf f (Coyoneda g m) (Wtf n) = let (x, b) = n m in f (g x) b

type Freer f = Free (Coyoneda f)

type CofreeWtf f = Cofree (Wtf f)

freerCofreeWtf :: Pairing (Freer f) (CofreeWtf f)
freerCofreeWtf = freeCofree coyonedaWtf

data GetPut s a where
  Get :: GetPut s s
  Put :: s -> GetPut s ()

send :: f a -> Freer f a
send = liftF . liftCoyoneda

getPutHandler :: s -> Wtf (GetPut s) s
getPutHandler s = Wtf \case
  Get -> (s, s)
  Put s' -> ((), s')

runGetPut :: forall s a. s -> Freer (GetPut s) a -> a
runGetPut s = \m -> freerCofreeWtf const m w
  where
    w :: CofreeWtf (GetPut s) ()
    w = Control.Comonad.Cofree.unfold (((),) . getPutHandler) s

main :: IO ()
main = print $ runGetPut (0 :: Int) do
  a <- send Get
  send $ Put 10
  b <- send Get
  send $ Put (b + 10)
  c <- send Get
  pure (a, b, c)
