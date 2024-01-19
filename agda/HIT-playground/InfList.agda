{-# OPTIONS --cubical #-}

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Foundations.Everything

private
  variable
    A B : Type

--------------------------------------------------------------------------------
-- Infinite list

infixr 5 _∷_

data InfList (A : Type) (d : A) : Type where
  [] : InfList A d
  _∷_ : (x : A) (xs : InfList A d) → InfList A d
  ext : [] ≡ d ∷ []

pattern repeat d = [] {d = d}

replicate : ∀ {d} → ℕ → A → InfList A d
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

extN : ∀ {d : A} (n : ℕ) → repeat d ≡ replicate n d
extN {d = d} zero = refl
extN {d = d} (suc n) = ext ∙ cong (d ∷_) (extN n)

--------------------------------------------------------------------------------
-- Example

_ : 1 ∷ 2 ∷ 3 ∷ repeat 0 ≡ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ repeat 0
_ = λ i → 1 ∷ 2 ∷ 3 ∷ extN 3 i
