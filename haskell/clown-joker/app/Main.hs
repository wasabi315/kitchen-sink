{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Bifunctor
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Sum
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Kind
import Data.Void
import GHC.Generics

class (Functor p, Bifunctor (Dissected p)) => Dissectable p where
  type Dissected p :: Type -> Type -> Type
  proceed ::
    Either (p j) (Dissected p c j, c) -> Either (j, Dissected p c j) (p c)
  plug ::
    a -> Dissected p a a -> p a

instance
  ( Generic1 p,
    Functor p,
    Bifunctor (GDissected (Rep1 p)),
    GDissectable (Rep1 p)
  ) =>
  Dissectable (Generically p)
  where
  type Dissected (Generically p) = GDissected (Rep1 p)
  proceed = second (Generically . to1) . gproceed . first (from1 . unGenerically)
  plug a = Generically . to1 . gplug a

newtype Generically p a = Generically {unGenerically :: p a}
  deriving stock (Functor)

class GDissectable (p :: Type -> Type) where
  type GDissected p :: Type -> Type -> Type
  gproceed ::
    Either (p j) (GDissected p c j, c) -> Either (j, GDissected p c j) (p c)
  gplug ::
    a -> GDissected p a a -> p a

newtype K2 c p q = K2 {unK2 :: c}
  deriving (Eq, Show)

instance Bifunctor (K2 c) where
  bimap _ _ (K2 c) = K2 c

instance GDissectable f => GDissectable (M1 i c f) where
  type GDissected (M1 i c f) = GDissected f
  gproceed = second M1 . gproceed . first unM1
  gplug a = M1 . gplug a

instance GDissectable U1 where
  type GDissected U1 = K2 Void
  gproceed (Left U1) = Right U1
  gproceed (Right (K2 v, _)) = absurd v
  gplug _ (K2 v) = absurd v

instance GDissectable (K1 i c) where
  type GDissected (K1 i c) = K2 Void
  gproceed (Left (K1 a)) = Right (K1 a)
  gproceed (Right (K2 v, _)) = absurd v
  gplug _ (K2 v) = absurd v

instance GDissectable Par1 where
  type GDissected Par1 = K2 ()
  gproceed (Left (Par1 j)) = Left (j, K2 ())
  gproceed (Right (_, c)) = Right $ Par1 c
  gplug a _ = Par1 a

instance (GDissectable p, GDissectable q) => GDissectable (p :+: q) where
  type GDissected (p :+: q) = GDissected p `Sum` GDissected q
  gproceed = \case
    Left (L1 pj) -> mindp $ gproceed $ Left pj
    Left (R1 qj) -> mindq $ gproceed $ Left qj
    Right (L2 pd, c) -> mindp $ gproceed $ Right (pd, c)
    Right (R2 pd, c) -> mindq $ gproceed $ Right (pd, c)
    where
      mindp (Left (j, pd)) = Left (j, L2 pd)
      mindp (Right pc) = Right $ L1 pc
      mindq (Left (j, qd)) = Left (j, R2 qd)
      mindq (Right qc) = Right $ R1 qc
  gplug a (L2 pd) = L1 $ gplug a pd
  gplug a (R2 qd) = R1 $ gplug a qd

instance (GDissectable p, GDissectable q) => GDissectable (p :*: q) where
  type
    GDissected (p :*: q) =
      (GDissected p `Product` Joker q) `Sum` (Clown p `Product` GDissected q)
  gproceed = \case
    Left (pj :*: qj) -> mindp (gproceed (Left pj)) qj
    Right (L2 (pd `Pair` Joker qj), c) -> mindp (gproceed (Right (pd, c))) qj
    Right (R2 (Clown pc `Pair` qd), c) -> mindq pc (gproceed (Right (qd, c)))
    where
      mindp (Left (j, pd)) qj = Left (j, L2 (pd `Pair` Joker qj))
      mindp (Right pc) qj = mindq pc (gproceed (Left qj))
      mindq pc (Left (j, qd)) = Left (j, R2 (Clown pc `Pair` qd))
      mindq pc (Right qc) = Right (pc :*: qc)
  gplug a (L2 (pd `Pair` Joker qa)) = gplug a pd :*: qa
  gplug a (R2 (Clown pa `Pair` qd)) = pa :*: gplug a qd

tcata :: (Recursive t, Dissectable (Base t)) => (Base t a -> a) -> t -> a
tcata f t = load t []
  where
    load = next . proceed . Left . project
    unload a [] = a
    unload a (pd : stk) = next (proceed (Right (pd, a))) stk
    next (Left (t', pd)) stk = load t' $ pd : stk
    next (Right pa) stk = unload (f pa) stk

data Expr
  = Val Int
  | Add Expr Expr
  | Mul Expr Expr
  | IfZero Expr Expr Expr
  deriving stock (Eq, Show)

makeBaseFunctor ''Expr

deriving stock instance Generic1 ExprF

deriving stock instance Show a => Show (ExprF a)

-- deriving via (Generically ExprF) instance Dissectable ExprF

data ExprD c j
  = Add0 j
  | Add1 c
  | Mul0 j
  | Mul1 c
  | IfZero0 j j
  | IfZero1 c j
  | IfZero2 c c

instance Bifunctor ExprD where
  bimap _ g (Add0 a) = Add0 (g a)
  bimap f _ (Add1 b) = Add1 (f b)
  bimap _ g (Mul0 a) = Mul0 (g a)
  bimap f _ (Mul1 b) = Mul1 (f b)
  bimap _ g (IfZero0 a b) = IfZero0 (g a) (g b)
  bimap f g (IfZero1 a b) = IfZero1 (f a) (g b)
  bimap f _ (IfZero2 a b) = IfZero2 (f a) (f b)

instance Dissectable ExprF where
  type Dissected ExprF = ExprD

  proceed (Left (ValF n)) = Right (ValF n)
  proceed (Left (AddF j k)) = Left (j, Add0 k)
  proceed (Left (MulF j k)) = Left (j, Mul0 k)
  proceed (Left (IfZeroF j k l)) = Left (j, IfZero0 k l)
  proceed (Right (Add0 j, c)) = Left (j, Add1 c)
  proceed (Right (Add1 c, d)) = Right (AddF c d)
  proceed (Right (Mul0 j, c)) = Left (j, Mul1 c)
  proceed (Right (Mul1 c, d)) = Right (MulF c d)
  proceed (Right (IfZero0 j k, c)) = Left (j, IfZero1 c k)
  proceed (Right (IfZero1 c j, d)) = Left (j, IfZero2 c d)
  proceed (Right (IfZero2 c d, e)) = Right (IfZeroF c d e)

  plug a (Add0 b) = AddF a b
  plug a (Add1 b) = AddF b a
  plug a (Mul0 b) = MulF a b
  plug a (Mul1 b) = MulF b a
  plug a (IfZero0 b c) = IfZeroF a b c
  plug a (IfZero1 b c) = IfZeroF b a c
  plug a (IfZero2 b c) = IfZeroF b c a

eval :: Expr -> Int
eval = tcata \case
  ValF n -> n
  AddF n m -> n + m
  MulF n m -> n * m
  IfZeroF p n m -> if p == 0 then n else m

main :: IO ()
main = do
  let expr = IfZero (Mul (Val 0) (Val 0)) (Add (Val 1) (Val 2)) (Val (-1))
  print $ eval expr
