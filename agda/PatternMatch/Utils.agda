{-# OPTIONS --guardedness #-}

module PatternMatch.Utils where

open import Data.Bool using ( T )
open import Data.Nat using ( ℕ; zero; _≡ᵇ_ )

--------------------------------------------------------------------------------
-- Misc

record Zero (n : ℕ) : Set where
  field
    isZero : T (n ≡ᵇ zero)

instance
  zeroZero : Zero zero
  zeroZero = _
