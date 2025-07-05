{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- Dissectable functors
-- Ref: McBride 2008 "Clowns to the left, Jokers to the right"

import Control.Monad
import Data.Bifunctor
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Sum
import Data.Functor.Foldable
import Data.Kind
import Data.Void
import GHC.Generics

--------------------------------------------------------------------------------

class (Functor p, Bifunctor (Dissected p)) => Dissectable p where
  type Dissected p :: Type -> Type -> Type
  right :: Either (p j) (Dissected p c j, c) -> Either (j, Dissected p c j) (p c)
  plug :: a -> Dissected p a a -> p a

class GDissectable p where
  type GDissected p :: Type -> Type -> Type
  gright :: Either (p j) (GDissected p c j, c) -> Either (j, GDissected p c j) (p c)
  gplug :: a -> GDissected p a a -> p a

instance (Generic1 p, Functor (Rep1 p), Bifunctor (GDissected (Rep1 p)), GDissectable (Rep1 p)) => Dissectable (Generically1 p) where
  type Dissected (Generically1 p) = GDissected (Rep1 p)
  right = second (Generically1 . to1) . gright . first (\(Generically1 x) -> from1 x)
  plug a = Generically1 . to1 . gplug a

--------------------------------------------------------------------------------

instance (GDissectable f) => GDissectable (M1 i c f) where
  type GDissected (M1 i c f) = GDissected f
  gright = second M1 . gright . first unM1
  gplug a = M1 . gplug a

--------------------------------------------------------------------------------

newtype WrappedDissected p a b = WrapDissected
  { unwrapDissected :: Dissected p a b
  }

deriving newtype instance (Bifunctor (Dissected p)) => Functor (WrappedDissected p a)

deriving newtype instance (Bifunctor (Dissected p)) => Bifunctor (WrappedDissected p)

instance (Dissectable p) => GDissectable (Rec1 p) where
  -- Replacing with Dissected p causes a reduction stack overflow!
  type GDissected (Rec1 p) = WrappedDissected p

  gright =
    bimap (second WrapDissected) Rec1
      . right
      . bimap unRec1 (first unwrapDissected)

  gplug a (WrapDissected x) = Rec1 $ plug a x

--------------------------------------------------------------------------------

newtype K2 c a b = K2 c deriving stock (Functor)

instance Bifunctor (K2 c) where
  bimap _ _ (K2 c) = K2 c

instance GDissectable U1 where
  type GDissected U1 = K2 Void
  gright = \case
    Left U1 -> Right U1
    Right (K2 v, _) -> absurd v
  gplug _ (K2 v) = absurd v

instance GDissectable (K1 i c) where
  type GDissected (K1 i c) = K2 Void
  gright = \case
    Left (K1 a) -> Right (K1 a)
    Right (K2 v, _) -> absurd v
  gplug _ (K2 v) = absurd v

--------------------------------------------------------------------------------

instance GDissectable Par1 where
  type GDissected Par1 = K2 ()
  gright = \case
    Left (Par1 j) -> Left (j, K2 ())
    Right (K2 (), c) -> Right $ Par1 c
  gplug a _ = Par1 a

--------------------------------------------------------------------------------

instance (GDissectable p, GDissectable q) => GDissectable (p :+: q) where
  type GDissected (p :+: q) = GDissected p `Sum` GDissected q

  gright = \case
    Left (L1 pj) -> mindp $ gright $ Left pj
    Left (R1 qj) -> mindq $ gright $ Left qj
    Right (L2 pd, c) -> mindp $ gright $ Right (pd, c)
    Right (R2 pd, c) -> mindq $ gright $ Right (pd, c)
    where
      mindp = \case
        Left (j, pd) -> Left (j, L2 pd)
        Right pc -> Right $ L1 pc
      mindq = \case
        Left (j, qd) -> Left (j, R2 qd)
        Right qc -> Right $ R1 qc

  gplug a = \case
    L2 pd -> L1 $ gplug a pd
    R2 qd -> R1 $ gplug a qd

--------------------------------------------------------------------------------

instance (GDissectable p, GDissectable q) => GDissectable (p :*: q) where
  type
    GDissected (p :*: q) =
      (GDissected p `Product` Joker q) `Sum` (Clown p `Product` GDissected q)

  gright = \case
    Left (pj :*: qj) -> mindp (gright (Left pj)) qj
    Right (L2 (pd `Pair` Joker qj), c) -> mindp (gright (Right (pd, c))) qj
    Right (R2 (Clown pc `Pair` qd), c) -> mindq pc (gright (Right (qd, c)))
    where
      mindp = \cases
        (Left (j, pd)) qj -> Left (j, L2 (pd `Pair` Joker qj))
        (Right pc) qj -> mindq pc (gright (Left qj))
      mindq pc = \case
        Left (j, qd) -> Left (j, R2 (Clown pc `Pair` qd))
        Right qc -> Right (pc :*: qc)

  gplug a = \case
    L2 (pd `Pair` Joker qa) -> gplug a pd :*: qa
    R2 (Clown pa `Pair` qd) -> pa :*: gplug a qd

--------------------------------------------------------------------------------

instance (Dissectable p, GDissectable q) => GDissectable (p :.: q) where
  type GDissected (p :.: q) = Product (Biff (Dissected p) q q) (GDissected q)

  gright = \case
    Left (Comp1 pqj) -> mindp (right (Left pqj))
    Right (Biff pd `Pair` qd, c) -> mindq (gright (Right (qd, c))) pd
    where
      mindp = \case
        Left (qj, pd) -> mindq (gright (Left qj)) pd
        Right pc -> Right $ Comp1 pc
      mindq = \cases
        (Left (j, qd)) pd -> Left (j, Biff pd `Pair` qd)
        (Right qc) pd -> mindp (right (Right (pd, qc)))

  gplug a (Biff pd `Pair` qd) = Comp1 $ plug (gplug a qd) pd

--------------------------------------------------------------------------------

tmap :: (Dissectable f) => (a -> b) -> f a -> f b
tmap f t = go (right (Left t))
  where
    go = \case
      Left (x, fd) -> go (right (Right (fd, f x)))
      Right fc -> fc

tcata :: (Recursive a, Dissectable (Base a)) => (Base a v -> v) -> a -> v
tcata alg = load []
  where
    load stk t = next stk $ right (Left (project t))
    next stk = \case
      Left (t, pd) -> load (pd : stk) t
      Right pv -> unload stk (alg pv)
    unload = \cases
      [] v -> v
      (pd : stk) v -> next stk $ right (Right (pd, v))

--------------------------------------------------------------------------------

data Free f a
  = Pure a
  | Free (f (Free f a))
  deriving stock (Generic, Generic1)

deriving instance (Show a, Show (f (Free f a))) => Show (Free f a)

data FreeF (f :: Type -> Type) a x
  = PureF a
  | FreeF (f x)
  deriving stock (Generic, Generic1)

type instance Base (Free f a) = FreeF f a

instance (Dissectable f) => Recursive (Free f a)

instance (Dissectable f) => Corecursive (Free f a)

deriving via
  (Generically1 (FreeF f a))
  instance
    (Dissectable f) => Dissectable (FreeF f a)

instance (Dissectable f) => Functor (FreeF f a) where
  fmap = tmap

deriving via
  (Generically1 (Free f))
  instance
    (Dissectable f) => Dissectable (Free f)

instance (Dissectable f) => Functor (Free f) where
  fmap = tmap

instance (Dissectable f) => Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance (Dissectable f) => Monad (Free f) where
  m >>= k = flip tcata m \case
    PureF x -> k x
    FreeF f -> Free f

deriving via (Generically1 []) instance Dissectable []

main :: IO ()
main = putStrLn "it typechecks"
