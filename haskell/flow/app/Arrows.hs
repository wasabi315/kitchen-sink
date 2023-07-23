{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Arrows where

import Control.Arrow
import Control.Category
import Data.Bool
import Data.Function (fix)
import Port
import Text.Show.Functions ()
import Prelude hiding (id, (.), (>>))

-- Diagram

data Flow a b where
  Id :: Flow a a
  Seq :: Flow a b -> Flow b c -> Flow a c
  Par :: Flow a b -> Flow c d -> Flow (a, c) (b, d)
  Dup :: Flow a (a, a)
  Void :: Flow a ()
  Fst :: Flow (a, b) a
  Snd :: Flow (a, b) b
  Embed :: (a -> b) -> Flow a b

deriving instance Show (Flow a b)

instance Category Flow where
  id = Id
  g . f = Seq f g

instance Cartesian Flow where
  fst = Fst
  snd = Snd
  dup = Dup
  f &&& g = Seq Dup (Par f g)
  void = Void

instance Arrow Flow where
  arr = Embed
  first f = Par f id
  second = Par id
  (***) = Par
  f &&& g = Seq Dup (Par f g)

box :: (a -> b) -> Port Flow r a -> Port Flow r b
box f = encode (Embed f)

ex1 :: Flow (a, b) (b, a)
ex1 = flow \(x :|: y) -> y :|: x

-- Mealy

newtype Mealy a b = Mealy {runMealy :: a -> (b, Mealy a b)}

instance Category Mealy where
  id = returnA
  Mealy f . Mealy g = Mealy \a ->
    let (b, g') = g a
        (c, f') = f b
     in (c, f' . g')

instance Cartesian Mealy where
  fst = arr Prelude.fst
  snd = arr Prelude.snd
  dup = arr \x -> (x, x)
  Mealy f &&& Mealy g = Mealy \a ->
    let (b, f') = f a
        (c, g') = g a
     in ((b, c), f' Port.&&& g')
  void = arr (const ())

instance Arrow Mealy where
  arr f = m where m = Mealy ((,m) . f)
  Mealy f *** Mealy g = Mealy \(a, c) ->
    let (b, f') = f a
        (d, g') = g c
     in ((b, d), f' *** g')

unfoldMealy :: s -> (s -> a -> (b, s)) -> Mealy a b
unfoldMealy s t = Mealy (fmap (`unfoldMealy` t) . t s)

feedMealy :: Mealy a b -> [a] -> [b]
feedMealy _ [] = []
feedMealy (Mealy f) (a : as) = let (b, m) = f a in b : feedMealy m as

data Cmd = Add Int | Sub Int

ex2 :: Mealy Cmd Int
ex2 = flow \cmd -> uncurry (-) ^$$ ((accumAdd $$ cmd) :|: (accumSub $$ cmd))
  where
    accumAdd, accumSub :: Mealy Cmd Int
    accumAdd = unfoldMealy 0 \s -> \case
      Add d -> let s' = s + d in (s', s')
      Sub _ -> (s, s)
    accumSub = unfoldMealy 0 \s -> \case
      Sub d -> let s' = s + d in (s', s')
      Add _ -> (s, s)

-- Naive Arrowised-FRP

type Time = Int

type DTime = Int

type Signal a = Time -> a

newtype SF a b = SF {unSF :: Signal a -> Signal b}

instance Category SF where
  id = SF id
  SF f . SF g = SF (f . g)

instance Cartesian SF where
  fst = arr Prelude.fst
  snd = arr Prelude.snd
  dup = arr \x -> (x, x)
  SF f &&& SF g = SF \s -> (,) <$> f s <*> g s
  void = constant ()

instance Arrow SF where
  arr f = SF (f .)
  SF f *** SF g = SF \s -> (,) <$> f (Port.fst . s) <*> g (Port.snd . s)

constant :: b -> SF a b
constant = arr . const

iPre :: a -> SF a a
iPre x = SF \b t -> if t == 0 then x else b (t - 1)

integral :: Num a => SF a a
integral = SF \b -> fix \f t -> if t == 0 then 0 else b t + f (t - 1)

reactimate :: SF a b -> [a] -> [b]
reactimate (SF f) input = f (input !!) <$> [0 .. length input - 1]

-- Applicative style is 'recovered' here!
fanController :: SF Float Bool
fanController =
  flow \tmp ->
    let th = bool 30.0 25.0 <$> fan'
        fan = (>=) <$> tmp <*> th
        fan' = iPre False $$ fan
     in fan

fanController' :: SF (Float, Float) Bool
fanController' =
  flow \(tmp :|: hmd) ->
    let di = calcDi <$> tmp <*> hmd
        fan = (>=) <$> di <*> th
        fan' = iPre False $$ fan
        th = bool 76.0 74.0 <$> fan'
     in fan
  where
    calcDi tmp hmd = 0.81 * tmp + 0.01 * hmd * (0.99 * tmp - 14.3) + 46.3
