{-# OPTIONS --cubical --safe #-}

open import Cubical.Data.Bool using ( Bool; true; false; if_then_else_ )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sigma using ( Σ-syntax; _,_; fst; snd )
open import Cubical.Foundations.Everything hiding ( assoc )
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

infixr 5 _·_ _·'_

data FreeMonoid (A : Type) : Type where
  ε : FreeMonoid A
  [_] : (x : A) → FreeMonoid A
  _·_ : (m₁ m₂ : FreeMonoid A) → FreeMonoid A

  εₗ : ∀ m₁ → ε · m₁ ≡ m₁
  εᵣ : ∀ m₁ → m₁ · ε ≡ m₁
  assoc : ∀ m₁ m₂ m₃ → m₁ · (m₂ · m₃) ≡ (m₁ · m₂) · m₃
  trunc : isSet (FreeMonoid A)

mutual

  -- slow append: (m ·' n) appends n next to the rightmost node in m
  _·'_ : ∀ {A} → FreeMonoid A → FreeMonoid A → FreeMonoid A
  ε ·' m₂ = m₂
  [ x ] ·' m₂ = [ x ] · m₂
  (m₁ · m₂) ·' m₃ = m₁ · (m₂ ·' m₃)
  εₗ m₁ i ·' m₂ = εₗ (m₁ ·' m₂) i
  εᵣ m₁ i ·' m₂ = m·n≡m·'n m₁ m₂ i
  assoc m₁ m₂ m₃ i ·' m₄ = assoc m₁ m₂ (m₃ ·' m₄) i
  trunc m₁ m₂ p q i j ·' m₃ =
    trunc (m₁ ·' m₃) (m₂ ·' m₃) (cong (_·' m₃) p) (cong (_·' m₃) q) i j

  m·n≡m·'n : ∀ {A} (m₁ m₂ : FreeMonoid A) → m₁ · m₂ ≡ m₁ ·' m₂
  m·n≡m·'n ε m₂ = εₗ m₂
  m·n≡m·'n [ x ] m₂ = refl
  m·n≡m·'n (m₁ · m₂) m₃ = sym (assoc _ _ _) ∙ cong (m₁ ·_) (m·n≡m·'n m₂ m₃)
  m·n≡m·'n (εₗ m₁ i) m₂ = isSet→isSet' trunc
    -- (m·n≡m·'n (ε · m₁) m₂) expanded
    (sym (assoc _ _ _) ∙ cong (ε ·_) (m·n≡m·'n m₁ m₂))
    (m·n≡m·'n m₁ m₂)
    (λ i → εₗ m₁ i · m₂)
    -- (λ i → εₗ m₁ i ·' m₂) expanded
    (εₗ (m₁ ·' m₂))
    i
  m·n≡m·'n (εᵣ m₁ i) m₂ = isSet→isSet' trunc
    -- (m·n≡m·'n (m₁ · ε) m₂) expanded
    (sym (assoc _ _ _) ∙ cong (m₁ ·_) (εₗ m₂))
    (m·n≡m·'n m₁ m₂)
    (λ i → εᵣ m₁ i · m₂)
    -- (λ i → εᵣ m₁ i ·' m₂) expanded
    (m·n≡m·'n m₁ m₂)
    i
  m·n≡m·'n (assoc m₁ m₂ m₃ i) m₄ = isSet→isSet' trunc
    -- (m·n≡m·'n (m₁ · m₂ · m₃) m₄) expanded
    (sym (assoc _ _ _) ∙ cong (m₁ ·_) (sym (assoc _ _ _) ∙ cong (m₂ ·_) (m·n≡m·'n m₃ m₄)))
    -- (m·n≡m·'n ((m₁ · m₂) · m₃) m₄) expanded
    (sym (assoc _ _ _) ∙ cong ((m₁ · m₂) ·_) (m·n≡m·'n m₃ m₄))
    (λ i → assoc m₁ m₂ m₃ i · m₄)
    -- (λ i → assoc m₁ m₂ m₃ i ·' m₄) expanded
    (assoc m₁ m₂ (m₃ ·' m₄))
    i
  m·n≡m·'n (trunc m₁ m₂ p q i j) m₃ = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ i → m·n≡m·'n (p i) m₃)
    (λ i → m·n≡m·'n (q i) m₃)
    (λ i → m·n≡m·'n m₁ m₃)
    (λ i → m·n≡m·'n m₂ m₃)
    (λ i j → trunc m₁ m₂ p q i j · m₃)
    -- (λ i j → trunc m₁ m₂ p q i j ·' m₃) expanded
    (trunc (m₁ ·' m₃) (m₂ ·' m₃) (cong (_·' m₃) p) (cong (_·' m₃) q))
    i j

module Elim {A} {P : FreeMonoid A → Type}
  (ε* : P ε)
  ([_]* : (x : A) → P [ x ])
  (_·*_ : ∀ {m₁ m₂} → P m₁ → P m₂ → P (m₁ · m₂))
  (εₗ* : ∀ {m₁} (m₁* : P m₁)
    → PathP (λ i → P (εₗ m₁ i)) (ε* ·* m₁*) m₁*)
  (εᵣ* : ∀ {m₁} (m₁* : P m₁)
    → PathP (λ i → P (εᵣ m₁ i)) (m₁* ·* ε*) (m₁*))
  (assoc* : ∀ {m₁ m₂ m₃} (m₁* : P m₁) (m₂* : P m₂) (m₃* : P m₃)
    → PathP (λ i → P (assoc m₁ m₂ m₃ i)) (m₁* ·* (m₂* ·* m₃*)) ((m₁* ·* m₂*) ·* m₃*))
  (trunc* : ∀ m₁ → isSet (P m₁))
  where

  f : (m₁ : FreeMonoid A) → P m₁
  f ε = ε*
  f [ x ] = [ x ]*
  f (m₁ · m₂) = f m₁ ·* f m₂
  f (εₗ m₁ i) = εₗ* (f m₁) i
  f (εᵣ m₁ i) = εᵣ* (f m₁) i
  f (assoc m₁ m₂ m₃ i) = assoc* (f m₁) (f m₂) (f m₃) i
  f (trunc m₁ m₂ p q i j) = isOfHLevel→isOfHLevelDep 2 trunc* (f m₁) (f m₂) (cong f p) (cong f q) (trunc m₁ m₂ p q) i j

module ElimProp {A} {P : FreeMonoid A → Type} (PProp : {m₁ : FreeMonoid A} → isProp (P m₁))
  (ε* : P ε)
  ([_]* : (x : A) → P [ x ])
  (_·*_ : ∀ {m₁ m₂} → P m₁ → P m₂ → P (m₁ · m₂))
  where

  f : (m₁ : FreeMonoid A) → P m₁
  f = Elim.f ε* [_]* _·*_
    (λ {m₁} m₁* → toPathP (PProp (transport (λ i → P (εₗ m₁ i)) (ε* ·* m₁*)) m₁*))
    (λ {m₁} m₁* → toPathP (PProp (transport (λ i → P (εᵣ m₁ i)) (m₁* ·* ε*)) m₁*))
    (λ {m₁ m₂ m₃} m₁* m₂* m₃* → toPathP (PProp (transport (λ i → P (assoc m₁ m₂ m₃ i)) (m₁* ·* (m₂* ·* m₃*))) ((m₁* ·* m₂*) ·* m₃*)))
    (λ _ → isProp→isSet PProp)

module Rec {A B : Type} (BType : isSet B)
  (ε* : B)
  ([_]* : (x : A) → B)
  (_·*_ : B → B → B)
  (εₗ* : ∀ (x : B) → ε* ·* x ≡ x)
  (εᵣ* : ∀ (x : B) → x ·* ε* ≡ x)
  (assoc* : ∀ (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  where

  f : (m₁ : FreeMonoid A) → B
  f = Elim.f ε* [_]* _·*_ εₗ* εᵣ* assoc* (const BType)

reverse : ∀ {A} → FreeMonoid A → FreeMonoid A
reverse =
  Rec.f trunc ε [_] (flip _·_) εᵣ εₗ (λ m₁ m₂ m₃ → sym (assoc m₃ m₂ m₁))

reverse-involutive : ∀ {A} (m₁ : FreeMonoid A) → reverse (reverse m₁) ≡ m₁
reverse-involutive =
  ElimProp.f
    (λ {m₁} → trunc (reverse (reverse m₁)) m₁)
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)

map : ∀ {A B} → (A → B) → FreeMonoid A → FreeMonoid B
map f = Rec.f trunc ε ([_] ∘ f) _·_ εₗ εᵣ assoc

map-id : ∀ {A} → map (idfun A) ≡ idfun (FreeMonoid A)
map-id = funExt $
  ElimProp.f
    (λ {m₁} → trunc (map (idfun _) m₁) m₁)
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)

map-∘ : ∀ {A B C} (f : B → C) (g : A → B) → map f ∘ map g ≡ map (f ∘ g)
map-∘ f g = funExt $
  ElimProp.f
    (λ {m₁} → trunc ((map f ∘ map g) m₁) (map (f ∘ g) m₁))
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)

join : ∀ {A} → FreeMonoid (FreeMonoid A) → FreeMonoid A
join = Rec.f trunc ε (idfun (FreeMonoid _)) _·_ εₗ εᵣ assoc

map-pure-join : ∀ {A} → join ∘ map [_] ≡ idfun (FreeMonoid A)
map-pure-join = funExt $
  ElimProp.f
    (λ {m₁} → trunc ((join ∘ map [_]) m₁) m₁)
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)
