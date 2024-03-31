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
    ℓ ℓ' : Level
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

{-

One cannot zip two Colist⊥s because zip does not preserve ⊥ as in the example below:

  zip [] (0 ∷ next ⊥) = []  -- ⊥ is lost

zip : Colist⊥ A → Colist⊥ B → Colist⊥ (A × B)
zip [] ⊥ = ⊥
zip [] (x ∷ xs) = []
zip [] (⊥-⊥ x i) = {!   !} -- impossible to prove [] ≡ ⊥
zip xs ys = {!   !}

-}

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
    P [] = Empty* , isPropEmpty*
    P ⊥ = Unit* , isPropUnit*
    P (_ ∷ _) = Unit* , isPropUnit*
    P (⊥-⊥ x i) = Unit* , isPropUnit*
    P (trunc xs ys p q i j) = isSetHProp _ _ (cong P p) (cong P q) i j

¬cons≡[] : ∀ {x : A} {xs} → ¬ x ∷ xs ≡ []
¬cons≡[] {ℓ} {A} p = lower (subst (λ xs → ⟨ P xs ⟩) p tt*)
  where
    P : Colist⊥ A → hProp ℓ
    P [] = Empty* , isPropEmpty*
    P ⊥ = Unit* , isPropUnit*
    P (_ ∷ _) = Unit* , isPropUnit*
    P (⊥-⊥ x i) = Unit* , isPropUnit*
    P (trunc xs ys p q i j) = isSetHProp _ _ (cong P p) (cong P q) i j

¬fromList≡[] : {xs : List A} → ¬ fromList⊥ xs ≡ []
¬fromList≡[] {xs = []} p = ¬⊥≡[] p
¬fromList≡[] {xs = x ∷ xs} p = ¬cons≡[] p

¬[]≡repeat : {x : A} → ¬ [] ≡ repeat x
¬[]≡repeat p = {!   !}

¬fromList⊥≡repeat : ∀ {x : A} {xs} → ¬ fromList⊥ xs ≡ repeat x
¬fromList⊥≡repeat p = {!   !}

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

Eventually⊥-tail : {x : A} {xs : ▹ Colist⊥ A}
  → Eventually⊥ (x ∷ xs)
  → ▸[ α ] Eventually⊥ (xs α)
Eventually⊥-tail ([] , p) α = [] , λ i → tail▹ (p i) α
Eventually⊥-tail (x ∷ xs , p) α = xs , λ i → tail▹ (p i) α

Eventually⊥→⊥ : (xs : Colist⊥ A) → Eventually⊥ xs → xs ≡ ⊥
Eventually⊥→⊥ =
  ElimProp.f (λ {xs} → isProp→ (trunc xs ⊥))
    (λ (_ , p) → Empty.rec (¬fromList≡[] p))
    (λ _ → refl)
    (λ x {xs} p q →
      x ∷ xs      ≡⟨ congS (x ∷_) (later-ext λ α → p α (Eventually⊥-tail q α)) ⟩
      x ∷ next ⊥  ≡⟨ ⊥-⊥ x ⟩
      ⊥           ∎)

Thm : ∀ {xs ys : Colist⊥ A}
  → Eventually⊥ xs
  → Eventually⊥ ys
  → xs ≡ ys
Thm p q = Eventually⊥→⊥ _ p ∙ sym (Eventually⊥→⊥ _ q)

¬Eventually⊥-repeat : {x : A} → ¬ Eventually⊥ (repeat x)
¬Eventually⊥-repeat = ¬fromList⊥≡repeat ∘ snd
