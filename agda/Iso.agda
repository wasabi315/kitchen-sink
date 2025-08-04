{-# OPTIONS --cubical-compatible --safe #-}

module Iso where

open import Level
open import Axiom.Extensionality.Propositional
open import Function.Base
open import Function.Bundles
open import Function.Properties.Inverse using (↔-sym)
open import Function.Properties.Inverse.HalfAdjointEquivalence
open import Relation.Binary.PropositionalEquality

private
  variable
    A B C D : Set
    F G H : A → Set

infixr 5 _,_

open Inverse

--------------------------------------------------------------------------------

record ⊤η : Set where
  constructor tt
record ⊤  : Set where
  no-eta-equality
  pattern
  constructor tt

record Ση (A : Set) (F : A → Set) : Set where
  constructor _,_
  field
    fstη : A
    sndη : F fstη

open Ση

_×η_ : Set → Set → Set
_×η_ A B = Ση A (λ _ → B)

record Σ (A : Set) (F : A → Set) : Set where
  no-eta-equality
  pattern
  constructor _,_
  field
    fst : A
    snd : F fst

open Σ

_×_ : Set → Set → Set
_×_ A B = Σ A (λ _ → B)

⊤η-weak : (x : ⊤) → tt ≡ x
⊤η-weak tt = refl

Ση-weak : (x : Σ A F) → fst x , snd x ≡ x
Ση-weak (x , y) = refl

Ση-≡,≡→≡ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Ση A F}
  → Ση (a₁ ≡ a₂) (λ p → subst F p b₁ ≡ b₂) → p₁ ≡ p₂
Ση-≡,≡→≡ (refl , refl) = refl

Ση-≡,≡→≡′ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Ση A F}
  → Ση (a₁ ≡ a₂) (λ p → b₁ ≡ subst F (sym p) b₂) → p₁ ≡ p₂
Ση-≡,≡→≡′ (refl , refl) = refl

Σ-≡,≡→≡ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A F}
  → Σ (a₁ ≡ a₂) (λ p → subst F p b₁ ≡ b₂) → p₁ ≡ p₂
Σ-≡,≡→≡ {p₁ = _ , _} {p₂ = _ , _} (refl , refl) = refl

Σ-≡,≡→≡′ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A F}
  → Σ (a₁ ≡ a₂) (λ p → b₁ ≡ subst F (sym p) b₂) → p₁ ≡ p₂
Σ-≡,≡→≡′ {p₁ = _ , _} {p₂ = _ , _} (refl , refl) = refl

--------------------------------------------------------------------------------

Ση-⊤ηₗ : Ση ⊤η F ↔ F tt
Ση-⊤ηₗ = mk↔ₛ′
  (λ (tt , x) → x)
  (λ x → tt , x)
  (λ _ → refl)
  (λ _ → refl)

Σ-⊤ηₗ : Σ ⊤η F ↔ F tt
Σ-⊤ηₗ = mk↔ₛ′
  (λ (tt , x) → x)
  (λ x → tt , x)
  (λ _ → refl)
  (λ { (_ , _) → refl })

Ση-⊤ₗ : Ση ⊤ F ↔ F tt
Ση-⊤ₗ = mk↔ₛ′
  (λ (tt , x) → x)
  (λ x → tt , x)
  (λ _ → refl)
  (λ { (tt , _) → refl })

Σ-⊤ₗ : Σ ⊤ F ↔ F tt
Σ-⊤ₗ = mk↔ₛ′
  (λ (tt , x) → x)
  (λ x → tt , x)
  (λ _ → refl)
  (λ { (tt , _) → refl })

×η-⊤ηᵣ : A ×η ⊤η ↔ A
×η-⊤ηᵣ = mk↔ₛ′
  (λ (a , _) → a)
  (λ a → a , tt)
  (λ _ → refl)
  (λ _ → refl)

×η-⊤ᵣ : A ×η ⊤ ↔ A
×η-⊤ᵣ = mk↔ₛ′
  (λ (a , _) → a)
  (λ a → a , tt)
  (λ _ → refl)
  (λ { (_ , tt) → refl })

×-⊤ηᵣ : A × ⊤η ↔ A
×-⊤ηᵣ = mk↔ₛ′
  (λ (a , _) → a)
  (λ a → a , tt)
  (λ _ → refl)
  (λ { (_ , _) → refl })

×-⊤ᵣ : A × ⊤ ↔ A
×-⊤ᵣ = mk↔ₛ′
  (λ (a , _) → a)
  (λ a → a , tt)
  (λ _ → refl)
  (λ { (_ , tt) → refl })

×η-comm : A ×η B ↔ B ×η A
×η-comm = mk↔ₛ′
  (λ (a , b) → b , a)
  (λ (b , a) → a , b)
  (λ _ → refl)
  (λ _ → refl)

×-comm : A × B ↔ B × A
×-comm = mk↔ₛ′
  (λ (a , b) → b , a)
  (λ (b , a) → a , b)
  (λ { (_ , _) → refl }) -- needs pattern matching
  (λ { (_ , _) → refl })

Ση-assoc : Ση (Ση A F) G ↔ Ση A (λ a → Ση (F a) λ b → G (a , b))
Ση-assoc = mk↔ₛ′
  (λ ((a , b) , c) → a , b , c)
  (λ (a , b , c) → ((a , b) , c))
  (λ _ → refl)
  (λ _ → refl)

Σ-assoc : Σ (Σ A F) G ↔ Σ A (λ a → Σ (F a) λ b → G (a , b))
Σ-assoc = mk↔ₛ′
  (λ ((a , b) , c) → a , b , c)
  (λ (a , b , c) → ((a , b) , c))
  (λ { (_ , _ , _) → refl })
  (λ { ((_ , _) , _) → refl })

Ση-curry : ((p : Ση A F) → G p) ↔ ((x : A) (y : F x) → G (x , y))
Ση-curry = mk↔ₛ′
  (λ f x y → f (x , y))
  (λ f (x , y) → f x y)
  (λ _ → refl)
  (λ _ → refl)

Σ-curry : Extensionality _ _ → ((p : Σ A F) → G p) ↔ ((x : A) (y : F x) → G (x , y))
Σ-curry funExt = mk↔ₛ′
  (λ f x y → f (x , y))
  (λ { f (x , y) → f x y }) -- needs pattern matching
  (λ _ → refl)
  (λ f → funExt λ { (x , y) → refl }) -- needs pattern matching and funext

Π-⊤ηₗ : ((x : ⊤η) → F x) ↔ F tt
Π-⊤ηₗ = mk↔ₛ′
  (λ f → f tt)
  (λ x _ → x)
  (λ _ → refl)
  (λ _ → refl)

Π-⊤ₗ : Extensionality _ _ → ((x : ⊤) → F x) ↔ F tt
Π-⊤ₗ funExt = mk↔ₛ′
  (λ f → f tt)
  (λ { x tt → x }) -- needs pattern matching
  (λ _ → refl)
  (λ f → funExt λ { tt → refl }) -- needs pattern matching and funext

→-⊤ηᵣ : (A → ⊤η) ↔ ⊤η
→-⊤ηᵣ = mk↔ₛ′
  (λ _ → tt)
  (λ x _ → x)
  (λ _ → refl)
  (λ _ → refl)

→-⊤ᵣ : Extensionality _ _ → (A → ⊤) ↔ ⊤
→-⊤ᵣ funExt = mk↔ₛ′
  (λ _ → tt)
  (λ x _ → x)
  (λ { tt → refl })
  (λ f → funExt λ x → ⊤η-weak (f x))

ΠΣη-dist : ((x : A) → Ση B F) ↔ (Ση ((x : A) → B) λ f → (x : A) → F (f x))
ΠΣη-dist = mk↔ₛ′
  (λ f → (λ x → fstη (f x)) , (λ x → sndη (f x)))
  (λ (f , g) x → f x , g x)
  (λ { (f , g) → refl })
  (λ _ → refl)

ΠΣ-dist : Extensionality _ _ → ((x : A) → Σ B F) ↔ Σ ((x : A) → B) (λ f → (x : A) → F (f x))
ΠΣ-dist funExt = mk↔ₛ′
  (λ f → (λ x → fst (f x)) , (λ x → snd (f x)))
  (λ (f , g) x → f x , g x)
  (λ { (f , g) → refl })
  (λ f → funExt λ x → Ση-weak (f x))

×η-cong : A ↔ B → C ↔ D → A ×η C ↔ B ×η D
×η-cong ab cd = mk↔ₛ′
  (λ (a , c) → ab .to a , cd .to c)
  (λ (b , d) → ab .from b , cd .from d)
  (λ (b , d) → cong₂ _,_ (strictlyInverseˡ ab b) (strictlyInverseˡ cd d))
  (λ (a , c) → cong₂ _,_ (strictlyInverseʳ ab a) (strictlyInverseʳ cd c))

×-cong : A ↔ B → C ↔ D → A × C ↔ B × D
×-cong ab cd = mk↔ₛ′
  (λ (a , c) → ab .to a , cd .to c)
  (λ (b , d) → ab .from b , cd .from d)
  (λ { (b , d) → cong₂ _,_ (strictlyInverseˡ ab b) (strictlyInverseˡ cd d) })
  (λ { (a , c) → cong₂ _,_ (strictlyInverseʳ ab a) (strictlyInverseʳ cd c) })

→-cong : Extensionality _ _ → A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→-cong funExt ab cd = mk↔ₛ′
  (λ f x → cd .to (f (ab .from x)))
  (λ f x → cd .from (f (ab .to x)))
  (λ f → funExt λ x → -- needs funext
    begin
      cd .to (cd .from (f (ab .to (ab .from x))))
    ≡⟨ strictlyInverseˡ cd _ ⟩
      f (ab .to (ab .from x))
    ≡⟨ cong f (strictlyInverseˡ ab _) ⟩
      f x
    ∎)
  (λ f → funExt λ x →
    begin
      cd .from (cd .to (f (ab .from (ab .to x))))
    ≡⟨ strictlyInverseʳ cd _ ⟩
      f (ab .from (ab .to x))
    ≡⟨ cong f (strictlyInverseʳ ab _) ⟩
      f x
    ∎)
  where open ≡-Reasoning

Ση-cong : (ab : A ↔ B) (fg : {x : A} → F x ↔ G x) → Ση A F ↔ Ση B (G ∘ ab .from)
Ση-cong {F = F} {G = G} ab fg = mk↔ₛ′
  (λ (a , c) → ab .to a , subst G (sym (right-inverse-of a)) (fg .to c))
  (λ (b , d) → ab .from b , fg .from d)
  (λ (b , d) →
    begin
      ab .to (ab .from b) , subst G (sym (right-inverse-of (ab .from b))) (fg .to (fg .from d))
    ≡⟨ cong (λ eq → ab .to (ab .from b) , subst G (sym eq) (fg .to (fg .from d))) (left-right b) ⟨
      ab .to (ab .from b) , subst G (sym (cong (ab .from) (left-inverse-of b))) (fg .to (fg .from d))
    ≡⟨ cong (λ eq → ab .to (ab .from b) , subst G eq (fg .to (fg .from d))) (sym-cong (left-inverse-of b)) ⟩
      ab .to (ab .from b) , subst G (cong (ab .from) (sym (left-inverse-of b))) (fg .to (fg .from d))
    ≡⟨ Ση-≡,≡→≡′ (left-inverse-of b , sym (subst-∘ (sym (left-inverse-of b)))) ⟩
      b , fg .to (fg .from d)
    ≡⟨ cong (b ,_) (strictlyInverseˡ fg d) ⟩
      b , d
    ∎)
  (λ (a , c) →
    begin
      ab .from (ab .to a) , fg .from (subst G (sym (right-inverse-of a)) (fg .to c))
    ≡⟨ cong (ab .from (ab .to a) ,_) (subst-application′ G (λ y → fg .from) (sym (right-inverse-of a))) ⟨
      ab .from (ab .to a) , subst F (sym (right-inverse-of a)) (fg .from (fg .to c))
    ≡⟨ Ση-≡,≡→≡′ ((right-inverse-of a) , cong (subst F (sym (right-inverse-of a))) (strictlyInverseʳ fg c)) ⟩
      a , c
    ∎)
  where
    open ≡-Reasoning
    open _≃_ (↔⇒≃ (↔-sym ab)) -- half-adjoint equivalence

Σ-cong : (ab : A ↔ B) (fg : {x : A} → F x ↔ G x) → Σ A F ↔ Σ B (G ∘ ab .from)
Σ-cong {F = F} {G = G} ab fg = mk↔ₛ′
  (λ (a , c) → ab .to a , subst G (sym (right-inverse-of a)) (fg .to c))
  (λ (b , d) → ab .from b , fg .from d)
  (λ { (b , d) →
    begin
      ab .to (ab .from b) , subst G (sym (right-inverse-of (ab .from b))) (fg .to (fg .from d))
    ≡⟨ cong (λ eq → ab .to (ab .from b) , subst G (sym eq) (fg .to (fg .from d))) (left-right b) ⟨
      ab .to (ab .from b) , subst G (sym (cong (ab .from) (left-inverse-of b))) (fg .to (fg .from d))
    ≡⟨ cong (λ eq → ab .to (ab .from b) , subst G eq (fg .to (fg .from d))) (sym-cong (left-inverse-of b)) ⟩
      ab .to (ab .from b) , subst G (cong (ab .from) (sym (left-inverse-of b))) (fg .to (fg .from d))
    ≡⟨ Σ-≡,≡→≡′ (left-inverse-of b , sym (subst-∘ (sym (left-inverse-of b)))) ⟩
      b , fg .to (fg .from d)
    ≡⟨ cong (b ,_) (strictlyInverseˡ fg d) ⟩
      b , d
    ∎ })
  (λ { (a , c) →
    begin
      ab .from (ab .to a) , fg .from (subst G (sym (right-inverse-of a)) (fg .to c))
    ≡⟨ cong (ab .from (ab .to a) ,_) (subst-application′ G (λ y → fg .from) (sym (right-inverse-of a))) ⟨
      ab .from (ab .to a) , subst F (sym (right-inverse-of a)) (fg .from (fg .to c))
    ≡⟨ Σ-≡,≡→≡′ ((right-inverse-of a) , cong (subst F (sym (right-inverse-of a))) (strictlyInverseʳ fg c)) ⟩
      a , c
    ∎ })
  where
    open ≡-Reasoning
    open _≃_ (↔⇒≃ (↔-sym ab)) -- half-adjoint equivalence

Π-cong : Extensionality _ _ → (ab : A ↔ B) (fg : {x : A} → F x ↔ G x) → ((x : A) → F x) ↔ ((y : B) → G (ab .from y))
Π-cong {F = F} {G = G} funExt ab fg = mk↔ₛ′
  (λ f y → fg .to (f (ab .from y)))
  (λ f x → subst F (right-inverse-of x) (fg .from (f (ab .to x))))
  (λ f → funExt λ y → -- needs funext
    begin
      fg .to (subst F (right-inverse-of (ab .from y)) (fg .from (f (ab .to (ab .from y)))))
    ≡⟨ cong (λ eq → fg .to (subst F eq (fg .from (f (ab .to (ab .from y)))))) (left-right y) ⟨
      fg .to (subst F (cong (ab .from) (left-inverse-of y)) (fg .from (f (ab .to (ab .from y)))))
    ≡⟨ subst-application F (λ x → fg .to) (left-inverse-of y) ⟨
      subst (G ∘ ab .from) (left-inverse-of y) (fg .to (fg .from (f (ab .to (ab .from y)))))
    ≡⟨ dcong (fg .to ∘ fg .from ∘ f) (left-inverse-of y) ⟩
      fg .to (fg .from (f y))
    ≡⟨ strictlyInverseˡ fg (f y) ⟩
      f y
    ∎)
  (λ f → funExt λ x → -- needs funext
    begin
      subst F (right-inverse-of x) (fg .from (fg .to (f (ab .from (ab .to x)))))
    ≡⟨ dcong (fg .from ∘ fg .to ∘ f) (right-inverse-of x) ⟩
      fg .from (fg .to (f x))
    ≡⟨ strictlyInverseʳ fg (f x) ⟩
      f x
    ∎)
  where
    open ≡-Reasoning
    open _≃_ (↔⇒≃ (↔-sym ab)) -- half-adjoint equivalence
