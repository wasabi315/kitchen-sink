{-# OPTIONS --guarded --cubical #-}

module Guarded.Partial where

open import Cubical.Foundations.Prelude

open import Guarded.Prims

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

--------------------------------------------------------------------------------
-- The partial monad

infixr 5 _>>=_

data Part (A : Type ℓ) : Type ℓ where
  now : A → Part A
  later : ▹ Part A → Part A

never : Part A
never = fix later

return : A → Part A
return = now

_>>=_ : Part A → (A → Part B) → Part B
now x >>= k = k x
later x >>= k = later λ α → x α >>= k
