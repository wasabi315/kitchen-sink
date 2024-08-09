{-# OPTIONS --cubical --guarded --exact-split #-}

module Guarded.PartialColist where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma using ( _×_; _,_ )

open import Guarded.Prims

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

--------------------------------------------------------------------------------

infixr 5 _∷_

data Colist (A : Type ℓ) : Type ℓ where
  [] : Colist A
  τ : ▹ Colist A → Colist A
  _∷_ : A → ▹ Colist A → Colist A

⊥ : Colist A
⊥ = fix τ

⊥-path : ⊥ {A = A} ≡ τ (next ⊥)
⊥-path = fix-path τ

--------------------------------------------------------------------------------

zip : Colist A → Colist B → Colist (A × B)
zip (τ xs) ys = τ λ α → zip (xs α) ys
zip xs@[] (τ ys) = τ λ α → zip xs (ys α)
zip xs@(_ ∷ _) (τ ys) = τ λ α → zip xs (ys α)
zip [] [] = []
zip [] (_ ∷ _) = []
zip (_ ∷ _) [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ α → zip (xs α) (ys α)

zip-⊥ˡ : ∀ {A B : Type ℓ} (xs : Colist B) → zip (⊥ {A = A}) xs ≡ ⊥
zip-⊥ˡ xs = fix λ ih▹ →
  zip ⊥ xs            ≡⟨ congS zip ⊥-path ≡$ xs ⟩
  τ (λ α → zip ⊥ xs)  ≡⟨ congS τ (later-ext λ α → ih▹ α) ⟩
  τ (λ α → ⊥)         ≡⟨ sym ⊥-path ⟩
  ⊥                   ∎
