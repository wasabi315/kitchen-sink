module Iso where

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Properties as List using ()
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry; uncurry)
open import Data.Product.Algebra using (×-assoc; ×-cong)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function using (_∘_; _$_; const; _↔_; mk↔; mk↔ₛ′; Inverse)
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔-trans; ↔-fun)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong′)

private
  variable
    m n : ℕ

infixr 40 _⇒_ _⇒ⁿ_
infixr 50 _*_ _*ⁿ_

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

atomic : Atom n → NF n
atomic α = List.[ unitⁿ ⇒ α ]

varⁿ : Fin n → NF n
varⁿ = atomic ∘ var

listⁿ : NF n → NF n
listⁿ = atomic ∘ list

_⇒ⁿ_ : NF n → NF n → NF n
_⇒ⁿ_ α = List.map λ { (β ⇒ i) → (α *ⁿ β) ⇒ i }

reduce : Ty n → NF n
reduce (var i) = varⁿ i
reduce unit    = unitⁿ
reduce (α * β) = reduce α *ⁿ reduce β
reduce (α ⇒ β) = reduce α ⇒ⁿ reduce β
reduce (list α) = listⁿ (reduce α)

--------------------------------------------------------------------------------

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

*ⁿ-homo-× : ∀ (α β : NF n) ρ → (⟦ α ⟧ⁿ ρ × ⟦ β ⟧ⁿ ρ) ↔ ⟦ α *ⁿ β ⟧ⁿ ρ
*ⁿ-homo-× []      β ρ = ×-identityˡ _
*ⁿ-homo-× (φ ∷ α) β ρ = ↔-trans (×-assoc _ _ _ _) (×-cong ↔-refl (*ⁿ-homo-× α β ρ))

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
