{-# OPTIONS --cubical --guarded #-}

module PartialTrunc where

open import Cubical.Foundations.Everything
open import Cubical.Data.List using ( List; []; _∷_ )
open import Cubical.Data.Empty as Empty using () renaming ( ⊥* to Empty*; isProp⊥* to isPropEmpty* )
open import Cubical.Data.Unit using ( Unit*; tt*; isPropUnit* )
open import Cubical.Data.Sigma using ( _,_ )
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
  -- All Colist⊥ that eventually ⊥ are equal to ⊥
  -- In other words, we are only interested in Colist⊥s that does not ⊥
  ⊥-⊥ : ∀ x → x ∷ next ⊥ ≡ ⊥
  trunc : isSet (Colist⊥ A)

tail▹ : Colist⊥ A → ▹ Colist⊥ A
tail▹ [] = next []
tail▹ ⊥ = next ⊥
tail▹ (x ∷ xs) = xs
tail▹ (⊥-⊥ x i) = next ⊥
tail▹ (trunc xs ys p q i j) α =
  trunc _ _ (λ i → tail▹ (p i) α) (λ i → tail▹ (q i) α) i j

repeat : A → Colist⊥ A
repeat x = fix (x ∷_)

repeat-unfold : ∀ {x : A} → repeat x ≡ x ∷ next (repeat x)
repeat-unfold = fix-path (_ ∷_)

fromList⊥ : List A → Colist⊥ A
fromList⊥ [] = ⊥
fromList⊥ (x ∷ xs) = x ∷ next (fromList⊥ xs)

cons-inj₂ : ∀ {x xs y ys} → Path (Colist⊥ A) (x ∷ xs) (y ∷ ys) → xs ≡ ys
cons-inj₂ p i α = tail▹ (p i) α

¬⊥≡[] : ¬ Path (Colist⊥ A) ⊥ []
¬⊥≡[] {ℓ} {A} p = lower (subst (λ xs → ⟨ P xs ⟩) p tt*)
  where
    P : Colist⊥ A → hProp ℓ
    P [] = Empty* , isPropEmpty*
    P ⊥ = Unit* , isPropUnit*
    P (_ ∷ _) = Unit* , isPropUnit*
    P (⊥-⊥ x i) = Unit* , isPropUnit*
    P (trunc xs ys p q i j) = isSetHProp (P xs) (P ys) (cong P p) (cong P q) i j

¬cons≡[] : ∀ {x xs} → ¬ Path (Colist⊥ A) (x ∷ xs) []
¬cons≡[] {ℓ} {A} p = lower (subst (λ xs → ⟨ P xs ⟩) p tt*)
  where
    P : Colist⊥ A → hProp ℓ
    P [] = Empty* , isPropEmpty*
    P ⊥ = Unit* , isPropUnit*
    P (_ ∷ _) = Unit* , isPropUnit*
    P (⊥-⊥ x i) = Unit* , isPropUnit*
    P (trunc xs ys p q i j) = isSetHProp (P xs) (P ys) (cong P p) (cong P q) i j

¬fromList≡[] : ∀ {xs : List A} → ¬ fromList⊥ xs ≡ []
¬fromList≡[] {xs = []} p = ¬⊥≡[] p
¬fromList≡[] {xs = x ∷ xs} p = ¬cons≡[] p

¬fromList⊥≡repeat : ∀ {x xs} → ¬ Path (Colist⊥ A) (fromList⊥ xs) (repeat x)
¬fromList⊥≡repeat p = {!   !}

--------------------------------------------------------------------------------

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

Eventually⊥→⊥ : {xs : Colist⊥ A} → Eventually⊥ xs → xs ≡ ⊥
Eventually⊥→⊥ {xs = []} (ys , p) = Empty.rec (¬fromList≡[] p)
Eventually⊥→⊥ {xs = ⊥} p = refl
Eventually⊥→⊥ {xs = x ∷ xs} p =
  x ∷ xs      ≡⟨ congS (x ∷_) (later-ext λ α → Eventually⊥→⊥ (Eventually⊥-tail p α)) ⟩
  x ∷ next ⊥  ≡⟨ ⊥-⊥ x ⟩
  ⊥           ∎
Eventually⊥→⊥ {xs = ⊥-⊥ x i} p = {!   !}
Eventually⊥→⊥ {xs = trunc xs ys p q i j} = {!   !}

Thm : ∀ {xs ys : Colist⊥ A}
  → Eventually⊥ xs
  → Eventually⊥ ys
  → xs ≡ ys
Thm p q = Eventually⊥→⊥ p ∙ sym (Eventually⊥→⊥ q)

¬Eventually⊥-repeat : {x : A} → ¬ Eventually⊥ (repeat x)
¬Eventually⊥-repeat = ¬fromList⊥≡repeat ∘ snd
