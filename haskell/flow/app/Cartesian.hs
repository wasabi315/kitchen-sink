{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}

module Cartesian where

import Control.Arrow
import Control.Category

class Category k => Cartesian k where
  fst :: k (a, b) a
  default fst :: Arrow k => k (a, b) a
  fst = arr Prelude.fst

  snd :: k (a, b) b
  default snd :: Arrow k => k (a, b) b
  snd = arr Prelude.snd

  dup :: k a (a, a)
  default dup :: Arrow k => k a (a, a)
  dup = arr \x -> (x, x)

  (&&&&) :: k a b -> k a c -> k a (b, c)
  default (&&&&) :: Arrow k => k a b -> k a c -> k a (b, c)
  (&&&&) = (&&&)

  void :: k a ()
  default void :: Arrow k => k a ()
  void = arr (const ())

instance Cartesian (->)

instance Monad m => Cartesian (Kleisli m)
