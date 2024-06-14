{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Kind
import GHC.TypeError

infix 4 /~

type (/~) :: forall k. k -> k -> Constraint
type family a /~ b where
  a /~ a = Unsatisfiable ('Text "Expected different types, but got the same type: " :<>: 'ShowType a)
  _ /~ _ = ()

data Void where
  Void :: (() /~ ()) => Void

ex :: Void -> a
ex f = case f of {}
