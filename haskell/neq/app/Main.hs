{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Kind
import GHC.TypeError

infix 4 /~

type (/~) :: k -> k -> Constraint
type family a /~ b where
  a /~ a = Unsatisfiable ('Text "Expected different types, but got the same type: " :<>: 'ShowType a)
  _ /~ _ = ()

data Void = (Void /~ Void) => Void

ex :: Void -> a
ex f = case f of {}
