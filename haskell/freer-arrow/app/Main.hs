-- Ref: Freer Arrows and Why You Need Them in Haskell (https://arxiv.org/abs/2506.12212)
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}

import Control.Arrow
import Control.Category
import Data.Bifunctor (bimap)
import Data.Profunctor
import Prelude hiding (id, (.))

main = pure ()

------------------------------------------------------------------------------

data FCA e x y where
  Hom :: (x -> y) -> FCA e x y
  Comp :: (x -> Either (a, c) w) -> e a b -> FCA e (Either (b, c) w) y -> FCA e x y

instance Category (FCA e) where
  id = Hom id
  Hom f . Hom g = Hom (f . g)
  Comp f' e y . Hom g = Comp (f' . g) e y
  f . Comp f' e y = Comp f' e (f . y)

instance Profunctor (FCA e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' e y) = Comp (f' . f) e (rmap g y)

instance Arrow (FCA e) where
  arr = Hom
  first (Hom f) = Hom (first f)
  first (Comp f a b) =
    Comp
      (first f >>> distr >>> left assoc)
      a
      (lmap (left unassoc >>> undistr) (first b))

instance ArrowChoice (FCA e) where
  left (Hom f) = Hom (left f)
  left (Comp f a b) = Comp (left f >>> assocsum) a (lmap unassocsum (left b))

distr :: (Either a b, c) -> Either (a, c) (b, c)
distr ~(eab, c) = bimap (,c) (,c) eab

undistr :: Either (a, c) (b, c) -> (Either a b, c)
undistr = either (\(a, c) -> (Left a, c)) (\(b, c) -> (Right b, c))

assoc :: ((a, b), c) -> (a, (b, c))
assoc ~((a, b), c) = (a, (b, c))

unassoc :: (a, (b, c)) -> ((a, b), c)
unassoc ~(a, (b, c)) = ((a, b), c)

assocsum :: Either (Either x y) z -> Either x (Either y z)
assocsum = either (either Left (Right . Left)) (Right . Right)

unassocsum :: Either x (Either y z) -> Either (Either x y) z
unassocsum = either (Left . Left) (either (Left . Right) Right)

interp :: (ArrowChoice arr) => (forall x y. e x y -> arr x y) -> FCA e a b -> arr a b
interp _ (Hom g) = arr g
interp h (Comp f x y) = arr f >>> left (first (h x)) >>> interp h y

-- Deep handlers
data DHandler e arr b c = Handler
  { dvalh :: arr b c,
    deffh :: forall x y z w. e x y -> arr (Either (y, z) w) c -> arr (Either (x, z) w) c
  }

handle :: (ArrowChoice arr) => DHandler e arr b c -> FCA e a b -> arr a c
handle h (Hom g) = arr g >>> dvalh h
handle h (Comp f x y) = arr f >>> deffh h x (handle h y)

-- interp defined in terms of handle
interp' :: (ArrowChoice arr) => (forall x y. e x y -> arr x y) -> FCA e a b -> arr a b
interp' h = handle Handler {dvalh = id, deffh = \e k -> left (first (h e)) >>> k}

-- Shallow handler
data SHandler e arr b c = SHandler
  { svalh :: arr b c,
    seffh :: forall x y z w. e x y -> (SHandler e arr b c -> arr (Either (y, z) w) c) -> arr (Either (x, z) w) c
  }

shandle :: (ArrowChoice arr) => SHandler e arr b c -> FCA e a b -> arr a c
shandle h (Hom g) = arr g >>> svalh h
shandle h (Comp f x y) = arr f >>> seffh h x (\h' -> shandle h' y)

-- deep handler defined in terms of shallow handler
handle' :: (ArrowChoice arr) => DHandler e arr b c -> FCA e a b -> arr a c
handle' h = shandle h'
  where
    h' = SHandler {svalh = dvalh h, seffh = \e k -> deffh h e (k h')}
