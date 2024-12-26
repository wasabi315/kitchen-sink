module Iso where

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Properties as Fin using ()
open import Data.List as List using (List; []; _∷_)
open import Data.List.Properties as List using ()
open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Homogeneous as Perm using (Permutation; refl; prep; swap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry; uncurry)
open import Data.Product.Algebra using (×-assoc; ×-comm)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function using (_∘_; _$_; const; flip; _↔_; mk↔; mk↔ₛ′; Inverse)
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔-trans; ↔-fun)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong′)

private
  variable
    m n : ℕ

infixr 40 _⇒_ _⇒ⁿ_
infixr 50 _*_ _*ⁿ_

--------------------------------------------------------------------------------
-- Some lemmas

×-identityˡ : (A : Set) → (⊤ × A) ↔ A
×-identityˡ _ = mk↔ₛ′ proj₂ (tt ,_) cong′ cong′

×-identityʳ : (A : Set) → (A × ⊤) ↔ A
×-identityʳ _ = mk↔ₛ′ proj₁ (_, tt) cong′ cong′

→-identityˡ : (A : Set) → (⊤ → A) ↔ A
→-identityˡ _ = mk↔ₛ′ (_$ tt) const cong′ cong′

→-distribˡ-× : (A B C : Set) → (A → B × C) ↔ ((A → B) × (A → C))
→-distribˡ-× _ _ _ =
  mk↔ₛ′ (λ f → (proj₁ ∘ f) , (proj₂ ∘ f)) (λ (f , g) x → (f x , g x)) cong′ cong′

curry↔ : (A B C : Set) → (A → B → C) ↔ (A × B → C)
curry↔ _ _ _ = mk↔ₛ′ uncurry curry cong′ cong′

module _ {A B : Set} (A↔B : A ↔ B) where
  open Inverse A↔B

  List-↔ : List A ↔ List B
  List-↔ =
    mk↔ₛ′ (List.map to) (List.map from)
      (λ xs → trans (sym (List.map-∘ xs)) (trans (List.map-cong strictlyInverseˡ xs) (List.map-id xs)))
      (λ ys → trans (sym (List.map-∘ ys)) (trans (List.map-cong strictlyInverseʳ ys) (List.map-id ys)))

--------------------------------------------------------------------------------

data Ty (n : ℕ) : Set where
  var  : (i : Fin n) → Ty n
  unit : Ty n
  _*_  : (α β : Ty n) → Ty n
  _⇒_  : (α β : Ty n) → Ty n
  list : (α : Ty n) → Ty n

⟦_⟧ : Ty n → (Vec Set n → Set)
⟦ var i  ⟧ ρ = Vec.lookup ρ i
⟦ unit   ⟧ ρ = ⊤
⟦ α * β  ⟧ ρ = ⟦ α ⟧ ρ × ⟦ β ⟧ ρ
⟦ α ⇒ β  ⟧ ρ = ⟦ α ⟧ ρ → ⟦ β ⟧ ρ
⟦ list α ⟧ ρ = List (⟦ α ⟧ ρ)

--------------------------------------------------------------------------------
-- Normal Form

mutual

  NF : ℕ → Set
  NF = List ∘ Factor

  data Factor (n : ℕ) : Set where
    _⇒_ : (α : NF n) (β : Atom n) → Factor n

  data Atom (n : ℕ) : Set where
    var  : (i : Fin n) → Atom n
    list : (α : NF n) → Atom n


mutual

  ⟦_⟧ⁿ : NF n → (Vec Set n → Set)
  ⟦ []    ⟧ⁿ ρ = ⊤
  ⟦ α ∷ β ⟧ⁿ ρ = ⟦ α ⟧ᶠ ρ × ⟦ β ⟧ⁿ ρ

  ⟦_⟧ᶠ : Factor n → (Vec Set n → Set)
  ⟦ α ⇒ β ⟧ᶠ ρ = ⟦ α ⟧ⁿ ρ → ⟦ β ⟧ᵃ ρ

  ⟦_⟧ᵃ : Atom n → (Vec Set n → Set)
  ⟦ var i  ⟧ᵃ ρ = Vec.lookup ρ i
  ⟦ list α ⟧ᵃ ρ = List (⟦ α ⟧ⁿ ρ)


unitⁿ : NF n
unitⁿ = []

_*ⁿ_ : NF n → NF n → NF n
_*ⁿ_ = List._++_

atom : Atom n → NF n
atom α = List.[ unitⁿ ⇒ α ]

varⁿ : Fin n → NF n
varⁿ = atom ∘ var

listⁿ : NF n → NF n
listⁿ = atom ∘ list

_⇒ⁿ_ : NF n → NF n → NF n
_⇒ⁿ_ α = List.map λ { (β ⇒ i) → (α *ⁿ β) ⇒ i }

reduce : Ty n → NF n
reduce (var i)  = varⁿ i
reduce unit     = unitⁿ
reduce (α * β)  = reduce α *ⁿ reduce β
reduce (α ⇒ β)  = reduce α ⇒ⁿ reduce β
reduce (list α) = listⁿ (reduce α)

--------------------------------------------------------------------------------

*ⁿ-homo-× : ∀ (α β : NF n) ρ → (⟦ α ⟧ⁿ ρ × ⟦ β ⟧ⁿ ρ) ↔ ⟦ α *ⁿ β ⟧ⁿ ρ
*ⁿ-homo-× []      β ρ = ×-identityˡ _
*ⁿ-homo-× (α ∷ β) γ ρ = ↔-trans (×-assoc _ _ _ _) (↔-refl ×-↔ (*ⁿ-homo-× β γ ρ))

module _ (ext : ∀ {a b} → Extensionality a b) where

  →-zeroʳ : (A : Set) → (A → ⊤) ↔ ⊤
  →-zeroʳ _ = mk↔ₛ′ (const tt) const cong′ (λ _ → ext {0ℓ} cong′)

  ⇒ⁿ-homo-→ : ∀ (α β : NF n) ρ → (⟦ α ⟧ⁿ ρ → ⟦ β ⟧ⁿ ρ) ↔ ⟦ α ⇒ⁿ β ⟧ⁿ ρ
  ⇒ⁿ-homo-→ α []          ρ = →-zeroʳ _
  ⇒ⁿ-homo-→ α (β ⇒ i ∷ γ) ρ =
    ↔-trans
      (→-distribˡ-× _ _ _)
      (↔-trans (curry↔ _ _ _) (↔-fun ext (*ⁿ-homo-× _ _ _) ↔-refl) ×-↔ ⇒ⁿ-homo-→ α γ ρ)

  reduce↔ : ∀ (α : Ty n) ρ → ⟦ α ⟧ ρ ↔ ⟦ reduce α ⟧ⁿ ρ
  reduce↔ (var i)  ρ = ↔-sym (↔-trans (×-identityʳ _) (→-identityˡ _))
  reduce↔ unit     ρ = ↔-refl
  reduce↔ (α * β)  ρ = ↔-trans (reduce↔ α ρ ×-↔ reduce↔ β ρ) (*ⁿ-homo-× _ _ _)
  reduce↔ (α ⇒ β)  ρ = ↔-trans (↔-fun ext (reduce↔ α ρ) (reduce↔ β ρ)) (⇒ⁿ-homo-→ _ _ _)
  reduce↔ (list α) ρ = ↔-trans (List-↔ (reduce↔ α ρ)) (↔-sym (↔-trans (×-identityʳ _) (→-identityˡ _)))

--------------------------------------------------------------------------------

mutual

  _≅ⁿ_ : NF n → NF n → Set
  _≅ⁿ_ = Permutation _≅ᶠ_

  data _≅ᶠ_ {n} : Factor n → Factor n → Set where
    _⇒_ : ∀ {α β γ δ} → α ≅ⁿ β → γ ≅ᵃ δ → α ⇒ γ ≅ᶠ β ⇒ δ

  data _≅ᵃ_ {n} : Atom n → Atom n → Set where
    var : ∀ {i j} → i ≡ j → var i ≅ᵃ var j
    list : ∀ {α β} → α ≅ⁿ β → list α ≅ᵃ list β

--------------------------------------------------------------------------------

Pointwise-⟦⟧ : ∀ {α β : NF n} {ρ}
  → Pointwise (λ γ δ → ⟦ γ ⟧ᶠ ρ ↔ ⟦ δ ⟧ᶠ ρ) α β
  → ⟦ α ⟧ⁿ ρ ↔ ⟦ β ⟧ⁿ ρ
Pointwise-⟦⟧ []          = ↔-refl
Pointwise-⟦⟧ (α≅β ∷ γ≅δ) = α≅β ×-↔ Pointwise-⟦⟧ γ≅δ

module _ (ext : ∀ {a b} → Extensionality a b) where

  {-# TERMINATING #-}
  mutual

    ≅→↔ⁿ : {α β : NF n} → α ≅ⁿ β → ∀ ρ → ⟦ α ⟧ⁿ ρ ↔ ⟦ β ⟧ⁿ ρ
    ≅→↔ⁿ (refl α≅β)           ρ = Pointwise-⟦⟧ (Pointwise.map (flip ≅→↔ᶠ ρ) α≅β)
    ≅→↔ⁿ (prep α≅β γ≅δ)       ρ = ≅→↔ᶠ α≅β ρ ×-↔ ≅→↔ⁿ γ≅δ ρ
    ≅→↔ⁿ (swap α≅β γ≅δ σ≅τ)   ρ =
      ↔-trans  (≅→↔ᶠ α≅β ρ ×-↔ ≅→↔ᶠ γ≅δ ρ ×-↔ ≅→↔ⁿ σ≅τ ρ)
        (↔-trans (↔-sym (×-assoc _ _ _ _))
          (↔-trans (×-comm _ _ ×-↔ ↔-refl)
            (×-assoc _ _ _ _)))
    ≅→↔ⁿ (Perm.trans α≅β γ≅δ) ρ = ↔-trans (≅→↔ⁿ α≅β ρ) (≅→↔ⁿ γ≅δ ρ)

    ≅→↔ᶠ : {α β : Factor n} → α ≅ᶠ β → ∀ ρ → ⟦ α ⟧ᶠ ρ ↔ ⟦ β ⟧ᶠ ρ
    ≅→↔ᶠ (α≅β ⇒ γ≅δ) ρ = ↔-fun ext (≅→↔ⁿ α≅β ρ) (≅→↔ᵃ γ≅δ ρ)

    ≅→↔ᵃ : {α β : Atom n} → α ≅ᵃ β → ∀ ρ → ⟦ α ⟧ᵃ ρ ↔ ⟦ β ⟧ᵃ ρ
    ≅→↔ᵃ (var refl) ρ = ↔-refl
    ≅→↔ᵃ (list α≅β) ρ = List-↔ (≅→↔ⁿ α≅β ρ)


  theorem : {α β : Ty n} → reduce α ≅ⁿ reduce β → ∀ ρ → ⟦ α ⟧ ρ ↔ ⟦ β ⟧ ρ
  theorem {α = α} {β} α≅β ρ =
    ↔-trans (reduce↔ ext α ρ)
      (↔-trans (≅→↔ⁿ α≅β ρ)
        (↔-sym (reduce↔ ext β ρ)))

  -- If we have a decision procedure for _≅ⁿ_, we can provide a function of type:
  --   (α β : Ty n) → Dec (∀ ρ → ⟦ α ⟧ ρ ↔ ⟦ β ⟧ ρ),
  -- which decides whether two types are isomorphic.
