{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Everything

data Free (F : Type₀ → Type₀ → Type₀) : Type₀ → Type₀ → Type₁ where
  [_] : ∀ {X Y} → F X Y → Free F X Y
  id : ∀ {X} → Free F X X
  _∘'_ : ∀ {X Y Z} → Free F Y Z → Free F X Y → Free F X Z

  ∘'-identityₗ : ∀ {X Y} (f : Free F X Y)
    → id ∘' f ≡ f
  ∘'-identityᵣ : ∀ {X Y} (f : Free F X Y)
    → f ∘' id ≡ f
  ∘'-assoc : ∀ {X Y Z W} (f : Free F Z W) (g : Free F Y Z) (h : Free F X Y)
    → f ∘' (g ∘' h) ≡ (f ∘' g) ∘' h
