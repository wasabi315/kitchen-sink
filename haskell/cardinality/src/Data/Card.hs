{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoStarIsType #-}

module Data.Card
  ( FiniteCard (..),
    KnownCard,
    card,
    cardOf,
    pattern Card,
    Generics (..),
  )
where

import Data.Finite qualified as F
import Data.Int
import Data.Proxy
import Data.Void
import Data.Word
import GHC.Generics
import GHC.TypeLits
import Unsafe.Coerce

type KnownCard a = KnownNat (Card a)

class KnownCard a => FiniteCard a where
  type Card a :: Nat
  toFinite :: a -> F.Finite (Card a)
  fromFinite :: F.Finite (Card a) -> a

card :: forall a. FiniteCard a => Integer
card = natVal @(Card a) Proxy

cardOf :: forall a. FiniteCard a => a -> Integer
cardOf _ = natVal @(Card a) Proxy

pattern Card :: forall a. FiniteCard a => Integer -> a
pattern Card c <- (cardOf -> c)

{-# COMPLETE Card #-}

instance KnownNat n => FiniteCard (F.Finite n) where
  type Card (F.Finite n) = n
  toFinite = id
  fromFinite = id

instance FiniteCard Int8 where
  type Card Int8 = 2 ^ 8
  toFinite n = F.finite $ fromIntegral n + 128
  fromFinite n = fromInteger $ F.getFinite n - 128

instance FiniteCard Int16 where
  type Card Int16 = 2 ^ 16
  toFinite n = F.finite $ fromIntegral n + 32768
  fromFinite n = fromInteger $ F.getFinite n - 32768

instance FiniteCard Int32 where
  type Card Int32 = 2 ^ 32
  toFinite n = F.finite $ fromIntegral n + 2147483648
  fromFinite n = fromInteger $ F.getFinite n - 2147483648

instance FiniteCard Int64 where
  type Card Int64 = 2 ^ 64
  toFinite n = F.finite $ fromIntegral n - 9223372036854775808
  fromFinite n = fromInteger $ F.getFinite n - 9223372036854775808

instance FiniteCard Word8 where
  type Card Word8 = 2 ^ 8
  toFinite = F.finite . fromIntegral
  fromFinite = fromInteger . F.getFinite

instance FiniteCard Word16 where
  type Card Word16 = 2 ^ 16
  toFinite = F.finite . fromIntegral
  fromFinite = fromInteger . F.getFinite

instance FiniteCard Word32 where
  type Card Word32 = 2 ^ 32
  toFinite = F.finite . fromIntegral
  fromFinite = fromInteger . F.getFinite

instance FiniteCard Word64 where
  type Card Word64 = 2 ^ 64
  toFinite = F.finite . fromIntegral
  fromFinite = fromInteger . F.getFinite

newtype Generics a = Generics a

instance (Generic a, FiniteCard' (Rep a)) => FiniteCard (Generics a) where
  type Card (Generics a) = Card' (Rep a)
  toFinite (Generics a) = toFinite' (from a)
  fromFinite n = Generics (to (fromFinite' n))

type KnownCard' f = KnownNat (Card' f)

class KnownCard' f => FiniteCard' f where
  type Card' f :: Nat
  toFinite' :: f a -> F.Finite (Card' f)
  fromFinite' :: F.Finite (Card' f) -> f a

instance FiniteCard' V1 where
  type Card' V1 = 0
  toFinite' x = case x of {}
  fromFinite' = unsafeCoerce

instance FiniteCard' U1 where
  type Card' U1 = 1
  toFinite' _ = F.finite 0
  fromFinite' _ = U1

instance FiniteCard c => FiniteCard' (K1 i c) where
  type Card' (K1 i c) = Card c
  toFinite' = toFinite . unK1
  fromFinite' = K1 . fromFinite

instance FiniteCard' f => FiniteCard' (M1 i c f) where
  type Card' (M1 i c f) = Card' f
  toFinite' = toFinite' . unM1
  fromFinite' = M1 . fromFinite'

instance (FiniteCard' f, FiniteCard' g, KnownCard' (f :+: g)) => FiniteCard' (f :+: g) where
  type Card' (f :+: g) = Card' f + Card' g
  toFinite' x = F.combineSum $ case x of
    L1 l -> Left (toFinite' l)
    R1 r -> Right (toFinite' r)
  fromFinite' n = case F.separateSum n of
    Left l -> L1 (fromFinite' l)
    Right r -> R1 (fromFinite' r)

instance (FiniteCard' f, FiniteCard' g, KnownCard' (f :*: g)) => FiniteCard' (f :*: g) where
  type Card' (f :*: g) = Card' f * Card' g
  toFinite' (l :*: r) = F.combineProduct (toFinite' l, toFinite' r)
  fromFinite' n = case F.separateProduct n of
    (l, r) -> fromFinite' l :*: fromFinite' r

deriving via Generics Void instance FiniteCard Void

deriving via Generics () instance FiniteCard ()

deriving via Generics Bool instance FiniteCard Bool

deriving via
  Generics (a, b)
  instance
    (FiniteCard a, FiniteCard b, KnownNat (Card a * Card b)) => FiniteCard (a, b)

deriving via
  Generics (Maybe a)
  instance
    (FiniteCard a, KnownNat (1 + Card a)) => FiniteCard (Maybe a)

deriving via
  Generics (Either a b)
  instance
    (FiniteCard a, FiniteCard b, KnownNat (Card a + Card b)) => FiniteCard (Either a b)
