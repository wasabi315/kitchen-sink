{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Control.Arrow.Effect.Nondet
  ( NonDet (..),
    runNonDet,
  )
where

import Control.Arrow.Effect
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------

data NonDet a b where
  Zero :: NonDet a b
  Plus :: Eff NonDet a b -> Eff NonDet a b -> NonDet a b

instance ArrowZero (Eff NonDet) where
  zeroArrow = Op Zero

instance ArrowPlus (Eff NonDet) where
  a <+> b = Op (Plus a b)

--------------------------------------------------------------------------------

runNonDet :: (ArrowPlus a) => Eff NonDet b c -> a b c
runNonDet =
  interpret \case
    Zero -> zeroArrow
    Plus a b -> runNonDet a <+> runNonDet b
