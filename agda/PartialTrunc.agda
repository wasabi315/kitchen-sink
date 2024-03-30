{-# OPTIONS --cubical --guardedness #-}

module PartialTrunc where

open import Cubical.Foundations.Everything
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Empty as Empty using () renaming ( ⊥* to Empty* )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Relation.Nullary using ( ¬_ )

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

--------------------------------------------------------------------------------

infixr 5 _∷_

data Colist⊥ (A : Type ℓ) : Type ℓ
record ∞Colist⊥ (A : Type ℓ) : Type ℓ

record ∞Colist⊥ A where
  coinductive
  constructor delay
  field
    force : Colist⊥ A

data Colist⊥ A where
  [] : Colist⊥ A
  ⊥ : Colist⊥ A
  _∷_ : (x : A) (xs : ∞Colist⊥ A) → Colist⊥ A
  -- All Colist⊥ that eventually ⊥ are equal to ⊥
  -- In other words, we are only interested in Colist⊥s that does not ⊥
  ⊥-⊥ : ∀ x → x ∷ delay ⊥ ≡ ⊥
  trunc : isSet (Colist⊥ A)

open ∞Colist⊥

∞Colist⊥-η : (xs : ∞Colist⊥ A) → xs ≡ delay (force xs)
force (∞Colist⊥-η xs i) = force xs

∞trunc : isSet (∞Colist⊥ A)
force (∞trunc xs ys p q i j) =
  trunc (force xs) (force ys) (cong force p) (cong force q) i j

repeat : A → Colist⊥ A
repeat x = x ∷ λ where .force → repeat x

fromList⊥ : List A → Colist⊥ A
fromList⊥ [] = ⊥
fromList⊥ (x ∷ xs) = x ∷ delay (fromList⊥ xs)

∞tail : Colist⊥ A → ∞Colist⊥ A
∞tail [] = delay []
∞tail ⊥ = delay ⊥
∞tail (x ∷ xs) = xs
∞tail (⊥-⊥ x i) = delay ⊥
∞tail (trunc xs ys p q i j) =
  ∞trunc (∞tail xs) (∞tail ys) (congS ∞tail p) (cong ∞tail q) i j

tail : Colist⊥ A → Colist⊥ A
tail [] = []
tail ⊥ = ⊥
tail (x ∷ xs) = force xs
tail (⊥-⊥ x i) = ⊥
tail (trunc xs ys p q i j) =
  trunc (tail xs) (tail ys) (congS tail p) (congS tail q) i j

∷-inj₂ : {x y : A} {xs ys : ∞Colist⊥ A}
  → x ∷ xs ≡ y ∷ ys
  → force xs ≡ force ys
∷-inj₂ p = cong tail p

¬⊥≡nil : ¬ Path (Colist⊥ A) ⊥ []
¬⊥≡nil {ℓ} {A} p = lower (subst P p tt*)
  where
    P : Colist⊥ A → Type ℓ
    isPropP : {xs : Colist⊥ A} → isProp (P xs)
    P [] = Empty*
    P ⊥ = Unit*
    P (x ∷ xs) = Unit*
    P (⊥-⊥ x i) = Unit*
    P (trunc xs ys p q i j) = {!   !}
    isPropP {xs = ⊥} tt* tt* = refl
    isPropP {xs = x ∷ xs} tt* tt* = refl
    isPropP {xs = ⊥-⊥ x i} tt* tt* = refl
    isPropP {xs = trunc xs ys p q i j} r s k = {!   !}

¬cons≡nil : ∀ {x xs} → ¬ Path (Colist⊥ A) (x ∷ xs) []
¬cons≡nil {ℓ} {A} p = lower (subst P p tt*)
  where
    P : Colist⊥ A → Type ℓ
    isPropP : {xs : Colist⊥ A} → isProp (P xs)
    P [] = Empty*
    P ⊥ = Unit*
    P (x ∷ xs) = Unit*
    P (⊥-⊥ x i) = Unit*
    P (trunc xs ys p q i j) = {!   !}
    isPropP {xs = ⊥} tt* tt* = refl
    isPropP {xs = x ∷ xs} tt* tt* = refl
    isPropP {xs = ⊥-⊥ x i} tt* tt* = refl
    isPropP {xs = trunc xs ys p q i j} r = {!   !}

¬fromList≡[] : ∀ {xs : List A} → ¬ fromList⊥ xs ≡ []
¬fromList≡[] {xs = []} p = ¬⊥≡nil p
¬fromList≡[] {xs = x ∷ xs} p = ¬cons≡nil p

--------------------------------------------------------------------------------

Eventually⊥ : {A : Type ℓ} (xs : Colist⊥ A) → Type ℓ
Eventually⊥ = fiber fromList⊥

Eventually⊥-fromList⊥ : (xs : List A) → Eventually⊥ (fromList⊥ xs)
Eventually⊥-fromList⊥ xs = xs , refl

Eventually⊥-⊥ : Eventually⊥ {A = A} ⊥
Eventually⊥-⊥ = Eventually⊥-fromList⊥ []

¬Eventually⊥-[] : ¬ Eventually⊥ {A = A} []
¬Eventually⊥-[] ([] , p) = ¬⊥≡nil p
¬Eventually⊥-[] (_ ∷ _ , p) = ¬cons≡nil p

Eventually⊥-tail : {xs : Colist⊥ A}
  → Eventually⊥ xs
  → Eventually⊥ (tail xs)
Eventually⊥-tail ([] , p) = [] , cong tail p
Eventually⊥-tail (x ∷ xs , p) = xs , cong tail p

lemma₀ : {xs : Colist⊥ A} → Eventually⊥ xs → xs ≡ ⊥
lemma₀ {xs = []} (ys , p) = Empty.rec (¬fromList≡[] p)
lemma₀ {xs = ⊥} p = refl
lemma₀ {xs = x ∷ xs} p =
  let q = Eventually⊥-tail p
   in {!   !}
  --   x ∷ xs
  -- ≡⟨ congS (x ∷_) {!   !} ⟩
  --   x ∷ delay (force xs)
  -- ≡⟨ congS (λ xs → x ∷ delay xs) (lemma₀ {xs = force xs} {!   !}) ⟩
  --   x ∷ delay ⊥
  -- ≡⟨ ⊥-⊥ x ⟩
  --   ⊥
  -- ∎
lemma₀ {xs = ⊥-⊥ x i} p = {!   !}
lemma₀ {xs = trunc xs ys p q i j} r = {!   !}

lemma₁ : {xs ys : Colist⊥ A}
  → Eventually⊥ xs
  → Eventually⊥ ys
  → xs ≡ ys
lemma₁ p q = lemma₀ p ∙ sym (lemma₀ q)

lemma₂ : (x : A) → ¬ Eventually⊥ (repeat x)
lemma₂ x p = {!   !}
