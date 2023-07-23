{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}

module Cartesian where

import Control.Arrow
import Control.Category

class Category k => Cartesian k where
  fst :: k (a, b) a
  snd :: k (a, b) b
  dup :: k a (a, a)
  (&&&&) :: k a b -> k a c -> k a (b, c)
  void :: k a ()

  default fst :: Arrow k => k (a, b) a
  default snd :: Arrow k => k (a, b) b
  default dup :: Arrow k => k a (a, a)
  default (&&&&) :: Arrow k => k a b -> k a c -> k a (b, c)
  default void :: Arrow k => k a ()
  fst = arr Prelude.fst
  snd = arr Prelude.snd
  dup = arr \x -> (x, x)
  (&&&&) = (&&&)
  void = arr (const ())

instance Cartesian (->)

instance Monad m => Cartesian (Kleisli m)
