{-# OPTIONS --cubical --guarded #-}

module PartialTrunc where

open import Cubical.Foundations.Everything
open import Cubical.Data.List using ( List; []; _∷_ )
open import Cubical.Data.Empty as Empty using () renaming ( ⊥* to Empty*; isProp⊥* to isPropEmpty* )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Relation.Nullary using ( ¬_ )

open import LaterPrims

private
  variable
    ℓ : Level
    A B : Type ℓ

--------------------------------------------------------------------------------

infixr 5 _∷_

data Colist⊥ (A : Type ℓ) : Type ℓ where
  [] ⊥ : Colist⊥ A
  _∷_ : (x : A) (xs : ▹ Colist⊥ A) → Colist⊥ A
  -- All Colist⊥s that eventually ⊥ are path equal to ⊥
  -- In other words, we are only interested in Colist⊥s that does not ⊥
  ⊥-⊥ : ∀ x → x ∷ next ⊥ ≡ ⊥
  trunc : isSet (Colist⊥ A)

module Elim {P : Colist⊥ A → Type ℓ}
  ([]* : P [])
  (⊥* : P ⊥)
  (_∷*_ : ∀ x {xs} (xs* : ▸[ α ] P (xs α)) → P (x ∷ xs))
  (⊥-⊥* : ∀ x → PathP (λ i → P (⊥-⊥ x i)) (x ∷* next ⊥*) ⊥*)
  (trunc* : ∀ xs → isSet (P xs))
  where

  f : (xs : Colist⊥ A) → P xs
  f [] = []*
  f ⊥ = ⊥*
  f (x ∷ xs) = x ∷* λ α → f (xs α)
  f (⊥-⊥ x i) = ⊥-⊥* x i
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* _ _ (cong f p) (cong f q) (trunc xs ys p q) i j

module ElimProp {P : Colist⊥ A → Type ℓ} (PProp : ∀ {xs} → isProp (P xs))
  ([]* : P [])
  (⊥* : P ⊥)
  (_∷*_ : ∀ x {xs} (xs* : ▸[ α ] P (xs α)) → P (x ∷ xs))
  where

  f : (xs : Colist⊥ A) → P xs
  f = Elim.f []* ⊥* _∷*_
    (λ x → toPathP (PProp (transport (λ i → P (⊥-⊥ x i)) (x ∷* next ⊥*)) ⊥*))
    (λ _ → isProp→isSet PProp)

module Rec (BType : isSet B)
  ([]* ⊥* : B)
  (_∷*_ : A → ▹ B → B)
  (⊥-⊥* : ∀ x → x ∷* next ⊥* ≡ ⊥*)
  where

  f : Colist⊥ A → B
  f = Elim.f []* ⊥* (λ x xs → x ∷* xs) ⊥-⊥* (const BType)

--------------------------------------------------------------------------------

map : (A → B) → Colist⊥ A → Colist⊥ B
map f = Rec.f trunc [] ⊥ (λ x ys → f x ∷ ys) (λ x → ⊥-⊥ (f x))

mutual

  {-# TERMINATING #-}
  zip : Colist⊥ A → Colist⊥ B → Colist⊥ (A × B)
  zip []       []       = []
  zip []       ⊥        = ⊥
  zip []       (y ∷ ys) = ⊥
  zip ⊥        []       = ⊥
  zip ⊥        ⊥        = ⊥
  zip ⊥        (y ∷ ys) = ⊥
  zip (x ∷ xs) []       = ⊥
  zip (x ∷ xs) ⊥        = ⊥
  zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ λ α → zip (xs α) (ys α)
  zip (⊥-⊥ x i) [] = ⊥
  zip (⊥-⊥ x i) ⊥ = ⊥
  zip [] (⊥-⊥ x k) = ⊥
  zip ⊥ (⊥-⊥ x k) = ⊥
  zip (x ∷ xs) (⊥-⊥ y k) =
    (congS ((x , y) ∷_) (later-ext λ α → zip-⊥ᵣ (xs α)) ∙ ⊥-⊥ (x , y)) k
  zip (⊥-⊥ x i) (y ∷ ys) =
    (congS ((x , y) ∷_) (later-ext λ α → zip-⊥ₗ (ys α)) ∙ ⊥-⊥ (x , y)) i
  zip (⊥-⊥ x i) (⊥-⊥ y k) = {!   !}
  zip [] (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zip []) q) (cong (zip []) q₁) k l
  zip ⊥ (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zip ⊥) q) (cong (zip ⊥) q₁) k l
  zip (x ∷ xs) (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zip (x ∷ xs)) q) (cong (zip (x ∷ xs)) q₁) k l
  zip (⊥-⊥ x i) (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zip (⊥-⊥ x i)) q) (cong (zip (⊥-⊥ x i)) q₁) k l
  zip (trunc xs xs₁ p p₁ i j) ys =
    trunc _ _ (cong (flip zip ys) p) (cong (flip zip ys) p₁) i j

  zip-⊥ₗ : (xs : Colist⊥ A) → zip {A = B} ⊥ xs ≡ ⊥
  zip-⊥ₗ = ElimProp.f (λ {xs} → trunc (zip ⊥ xs) ⊥) refl refl (λ _ _ → refl)

  zip-⊥ᵣ : (xs : Colist⊥ A) → zip {B = B} xs ⊥ ≡ ⊥
  zip-⊥ᵣ = ElimProp.f (λ {xs} → trunc (zip xs ⊥) ⊥) refl refl (λ _ _ → refl)

tail▹ : Colist⊥ A → ▹ Colist⊥ A
tail▹ [] = next []
tail▹ ⊥ = next ⊥
tail▹ (x ∷ xs) = xs
tail▹ (⊥-⊥ x i) = next ⊥
tail▹ (trunc xs ys p q i j) α =
  trunc _ _ (λ i → tail▹ (p i) α) (λ i → tail▹ (q i) α) i j

repeat : A → Colist⊥ A
repeat x = fix (x ∷_)

fromList⊥ : List A → Colist⊥ A
fromList⊥ [] = ⊥
fromList⊥ (x ∷ xs) = x ∷ next (fromList⊥ xs)

--------------------------------------------------------------------------------

repeat-unfold : {x : A} → repeat x ≡ x ∷ next (repeat x)
repeat-unfold = fix-path (_ ∷_)

⊥-⊥-path : {x : A} → PathP (λ i → ⊥-⊥ x i ≡ ⊥) (⊥-⊥ x) refl
⊥-⊥-path {x = x} i j = ⊥-⊥ x (i ∨ j)

cons-inj₂ : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ p = cong tail▹ p

¬⊥≡[] : ¬ Path (Colist⊥ A) ⊥ []
¬⊥≡[] {ℓ} {A} p = lower (subst (λ xs → ⟨ P xs ⟩) p tt*)
  where
    P : Colist⊥ A → hProp ℓ
    P = Rec.f isSetHProp
      (Empty* , isPropEmpty*)
      (Unit* , isPropUnit*)
      (λ _ _ → Unit* , isPropUnit*)
      (const refl)

¬cons≡[] : ∀ {x : A} {xs} → ¬ x ∷ xs ≡ []
¬cons≡[] {ℓ} {A} p = lower (subst (λ xs → ⟨ P xs ⟩) p tt*)
  where
    P : Colist⊥ A → hProp ℓ
    P = Rec.f isSetHProp
      (Empty* , isPropEmpty*)
      (Unit* , isPropUnit*)
      (λ _ _ → Unit* , isPropUnit*)
      (const refl)

¬fromList≡[] : {xs : List A} → ¬ fromList⊥ xs ≡ []
¬fromList≡[] {xs = []} p = ¬⊥≡[] p
¬fromList≡[] {xs = x ∷ xs} p = ¬cons≡[] p

¬[]≡repeat : {x : A} → ¬ [] ≡ repeat x
¬[]≡repeat p = ¬cons≡[] (sym (p ∙ repeat-unfold))

-- Is this provable?
¬⊥≡repeat : {x : A} → ¬ ⊥ ≡ repeat x
¬⊥≡repeat = {!   !}

¬fromList⊥≡repeat : ∀ {x : A} {xs} → ¬ fromList⊥ xs ≡ repeat x
¬fromList⊥≡repeat {xs = []} p = ¬⊥≡repeat p
¬fromList⊥≡repeat {x = x} {_ ∷ xs} p = {!   !}

--------------------------------------------------------------------------------
-- Eventually ⊥

Eventually⊥ : {A : Type ℓ} (xs : Colist⊥ A) → Type ℓ
Eventually⊥ = fiber fromList⊥

Eventually⊥-fromList⊥ : (xs : List A) → Eventually⊥ (fromList⊥ xs)
Eventually⊥-fromList⊥ xs = xs , refl

Eventually⊥-⊥ : Eventually⊥ {A = A} ⊥
Eventually⊥-⊥ = Eventually⊥-fromList⊥ []

¬Eventually⊥-[] : ¬ Eventually⊥ {A = A} []
¬Eventually⊥-[] = ¬fromList≡[] ∘ snd

Eventually⊥-tail▹ : {xs : Colist⊥ A}
  → Eventually⊥ xs
  → ▸[ α ] Eventually⊥ (tail▹ xs α)
Eventually⊥-tail▹ ([] , p) α = [] , λ i → tail▹ (p i) α
Eventually⊥-tail▹ (x ∷ xs , p) α = xs , λ i → tail▹ (p i) α

Eventually⊥→⊥ : (xs : Colist⊥ A) → Eventually⊥ xs → xs ≡ ⊥
Eventually⊥→⊥ =
  ElimProp.f (λ {xs} → isProp→ (trunc xs ⊥))
    (Empty.rec ∘ ¬fromList≡[] ∘ snd)
    (const refl)
    (λ x {xs} p q →
      x ∷ xs      ≡[ i ]⟨ x ∷ (λ α → p α (Eventually⊥-tail▹ q α) i) ⟩
      x ∷ next ⊥  ≡⟨ ⊥-⊥ x ⟩
      ⊥           ∎)

thm : ∀ {xs ys : Colist⊥ A}
  → Eventually⊥ xs
  → Eventually⊥ ys
  → xs ≡ ys
thm p q = Eventually⊥→⊥ _ p ∙ sym (Eventually⊥→⊥ _ q)

¬Eventually⊥-repeat : {x : A} → ¬ Eventually⊥ (repeat x)
¬Eventually⊥-repeat = ¬fromList⊥≡repeat ∘ snd
