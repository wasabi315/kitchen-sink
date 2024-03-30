{-# OPTIONS --cubical --guarded #-}

module PartialColist where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool using ( Bool; true; false; if_then_else_; _and_; and-idem )

open import LaterPrims

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

--------------------------------------------------------------------------------

infixr 5 _∷_ _∷▹_

data PartialColist (A : Type ℓ) : Type ℓ where
  [] : PartialColist A
  _∷_ : (x : A) (xs : ▹ PartialColist A) → PartialColist A
  τ : (xs : ▹ PartialColist A) → PartialColist A
  τ⁻ : ∀ xs → τ (next xs) ≡ xs
  trunc : isSet (PartialColist A)

_∷▹_ : A → PartialColist A → PartialColist A
x ∷▹ xs = x ∷ next xs

⊥ : PartialColist A
⊥ = fix τ

map : (A → B) → PartialColist A → PartialColist B
map f [] = []
map f (x ∷ xs) = f x ∷ λ α → map f (xs α)
map f (τ xs) = τ λ α → map f (xs α)
map f (τ⁻ xs i) = τ⁻ (map f xs) i
map f (trunc xs ys p q i j) = trunc _ _ (cong (map f) p) (cong (map f) q) i j

filter : (A → Bool) → PartialColist A → PartialColist A
filter f [] = []
filter f (x ∷ xs) = (if f x then (x ∷_) else τ) λ α → filter f (xs α)
filter f (τ xs) = τ λ α → filter f (xs α)
filter f (τ⁻ xs i) = τ⁻ (filter f xs) i
filter f (trunc xs ys p q i j) = trunc _ _ (cong (filter f) p) (cong (filter f) q) i j

--------------------------------------------------------------------------------
-- Properties

filter-eqᵗ : ∀ {f : A → Bool} {x}
  → f x ≡ true
  → ∀ xs → filter f (x ∷ xs) ≡ x ∷ λ α → filter f (xs α)
filter-eqᵗ {f = f} {x} p xs =
    (if f x then (x ∷_) else τ) (λ α → filter f (xs α))
  ≡⟨ cong (if_then (x ∷_) else τ) p ≡$ (λ α → filter f (xs α)) ⟩
    x ∷ (λ α → filter f (xs α))
  ∎

filter-eqᶠ : ∀ {f : A → Bool} {x}
  → f x ≡ false
  → ∀ xs → filter f (x ∷ xs) ≡ τ λ α → filter f (xs α)
filter-eqᶠ {f = f} {x} p xs =
    (if f x then (x ∷_) else τ) (λ α → filter f (xs α))
  ≡⟨ cong (if_then (x ∷_) else τ) p ≡$ (λ α → filter f (xs α)) ⟩
    τ (λ α → filter f (xs α))
  ∎

filter-eqᶠ′ : ∀ {f : A → Bool} {x}
  → f x ≡ false
  → ∀ xs → filter f (x ∷ next xs) ≡ filter f xs
filter-eqᶠ′ {f = f} {x} p xs =
    filter f (x ∷ next xs)
  ≡⟨ filter-eqᶠ p (next xs) ⟩
    τ (λ _ → filter f xs)
  ≡⟨ τ⁻ (filter f xs) ⟩
    filter f xs
  ∎

filter-filter : ∀ (f g : A → Bool) xs
  → filter f (filter g xs) ≡ filter (λ x → g x and f x) xs
filter-filter f g [] = refl
filter-filter f g (x ∷ xs) with g x
... | false = cong τ (later-ext λ α → filter-filter f g (xs α))
... | true = cong (if f x then x ∷_ else τ) (later-ext λ α → filter-filter f g (xs α))
filter-filter f g (τ xs) = cong τ (later-ext λ α → filter-filter f g (xs α))
filter-filter f g (τ⁻ xs i) j = τ⁻ (filter-filter f g xs j) i
filter-filter f g (trunc xs ys p q i j) k =
  trunc _ _ (λ l → filter-filter f g (p l) k) (λ l → filter-filter f g (q l) k) i j

filter-stable : ∀ (f : A → Bool) xs → filter f (filter f xs) ≡ filter f xs
filter-stable f xs =
    filter f (filter f xs)
  ≡⟨ filter-filter f f xs ⟩
    filter (λ x → f x and f x) xs
  ≡⟨ cong filter (funExt λ x → and-idem (f x)) ≡$ xs ⟩
    filter f xs
  ∎
