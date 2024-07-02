{-# OPTIONS --guardedness --safe #-}

module PartialColist where

open import Level
open import Data.Bool using ( Bool; true; false )
open import Data.Product using ( _×_; _,_ )

private
  variable
    ℓ ℓ' : Level
    A B : Set ℓ

infixr 5 _∷_
infix 4 _≈_ _∞≈_

--------------------------------------------------------------------------------

data PartialColist (A : Set ℓ) : Set ℓ
record ∞PartialColist (A : Set ℓ) : Set ℓ

data PartialColist A where
  [] : PartialColist A
  τ : (xs : ∞PartialColist A) → PartialColist A
  _∷_ : (x : A) (xs : ∞PartialColist A) → PartialColist A

record ∞PartialColist A where
  coinductive
  constructor delay
  field force : PartialColist A

open ∞PartialColist

⊥ : PartialColist A
∞⊥ : ∞PartialColist A
⊥ = τ ∞⊥
force ∞⊥ = τ ∞⊥

--------------------------------------------------------------------------------
-- Strong Bisimulation

data _≈_ {A : Set ℓ} : (xs ys : PartialColist A) → Set ℓ
record _∞≈_ {A : Set ℓ} (xs ys : ∞PartialColist A) : Set ℓ

data _≈_ {A} where
  [] : [] ≈ []
  τ : ∀ {xs ys} (p : xs ∞≈ ys) → τ xs ≈ τ ys
  _∷_ : ∀ x {xs ys} (p : xs ∞≈ ys) → x ∷ xs ≈ x ∷ ys

record _∞≈_ xs ys where
  coinductive
  constructor delay
  field force : force xs ≈ force ys

open _∞≈_

≈-refl : {xs : PartialColist A} → xs ≈ xs
∞≈-refl : {xs : ∞PartialColist A} → xs ∞≈ xs
≈-refl {xs = []} = []
≈-refl {xs = τ xs} = τ ∞≈-refl
≈-refl {xs = x ∷ xs} = x ∷ ∞≈-refl
force ∞≈-refl = ≈-refl

≈-sym : {xs ys : PartialColist A} → xs ≈ ys → ys ≈ xs
∞≈-sym : {xs ys : ∞PartialColist A} → xs ∞≈ ys → ys ∞≈ xs
≈-sym [] = []
≈-sym (τ p) = τ (∞≈-sym p)
≈-sym (x ∷ p) = x ∷ ∞≈-sym p
force (∞≈-sym p) = ≈-sym (force p)

≈-trans : {xs ys zs : PartialColist A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
∞≈-trans : {xs ys zs : ∞PartialColist A} → xs ∞≈ ys → ys ∞≈ zs → xs ∞≈ zs
≈-trans [] [] = []
≈-trans (τ p) (τ q) = τ (∞≈-trans p q)
≈-trans (x ∷ p) (.x ∷ q) = x ∷ ∞≈-trans p q
force (∞≈-trans p q) = ≈-trans (force p) (force q)

--------------------------------------------------------------------------------

zip : PartialColist A → PartialColist B → PartialColist (A × B)
∞zip : ∞PartialColist A → ∞PartialColist B → ∞PartialColist (A × B)
zip (τ xs) (τ ys) = τ (∞zip xs ys)
zip (τ xs) ys = τ (∞zip xs (delay ys))
zip xs (τ ys) = τ (∞zip (delay xs) ys)
zip [] ys = []
zip xs [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ ∞zip xs ys
force (∞zip xs ys) = zip (force xs) (force ys)

zip-⊥ˡ : {A B : Set ℓ} (xs : PartialColist B) → zip (⊥ {A = A}) xs ≈ ⊥
∞zip-⊥ˡ : {A B : Set ℓ} (xs : ∞PartialColist B) → ∞zip (∞⊥ {A = A}) xs ∞≈ ∞⊥
zip-⊥ˡ [] = τ (∞zip-⊥ˡ (delay []))
zip-⊥ˡ (τ xs) = τ (∞zip-⊥ˡ xs)
zip-⊥ˡ (x ∷ xs) = τ (∞zip-⊥ˡ (delay (x ∷ xs)))
force (∞zip-⊥ˡ xs) = zip-⊥ˡ (force xs)

zip-⊥ʳ : {A B : Set ℓ} (xs : PartialColist A) → zip xs (⊥ {A = B}) ≈ ⊥
∞zip-⊥ʳ : {A B : Set ℓ} (xs : ∞PartialColist A) → ∞zip xs (∞⊥ {A = B}) ∞≈ ∞⊥
zip-⊥ʳ [] = τ (∞zip-⊥ʳ (delay []))
zip-⊥ʳ (τ xs) = τ (∞zip-⊥ʳ xs)
zip-⊥ʳ (x ∷ xs) = τ (∞zip-⊥ʳ (delay (x ∷ xs)))
force (∞zip-⊥ʳ xs) = zip-⊥ʳ (force xs)

filter : (A → Bool) → PartialColist A → PartialColist A
∞filter : (A → Bool) → ∞PartialColist A → ∞PartialColist A
filter p [] = []
filter p (τ xs) = τ (∞filter p xs)
filter p (x ∷ xs) with p x
... | true = x ∷ ∞filter p xs
... | false = τ (∞filter p xs)
force (∞filter p xs) = filter p (force xs)

filter-⊥ : (p : A → Bool) → filter p ⊥ ≈ ⊥
∞filter-⊥ : (p : A → Bool) → ∞filter p ∞⊥ ∞≈ ∞⊥
filter-⊥ p = τ (∞filter-⊥ p)
force (∞filter-⊥ p) = filter-⊥ p
