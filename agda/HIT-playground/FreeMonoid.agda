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
  _·_ : (m n : FreeMonoid A) → FreeMonoid A

  εₗ : ∀ m → ε · m ≡ m
  εᵣ : ∀ m → m · ε ≡ m
  assoc : ∀ m n o → m · (n · o) ≡ (m · n) · o
  trunc : isSet (FreeMonoid A)

mutual

  -- slow append: (m ·' n) appends n next to the rightmost node of m
  _·'_ : ∀ {A} → FreeMonoid A → FreeMonoid A → FreeMonoid A
  ε ·' n = n
  [ x ] ·' n = [ x ] · n
  (m · n) ·' o = m · (n ·' o)
  εₗ m i ·' n = εₗ (m ·' n) i
  εᵣ m i ·' n = m·n≡m·'n m n i
  assoc m n o i ·' p = assoc m n (o ·' p) i
  trunc m n p q i j ·' o =
    trunc (m ·' o) (n ·' o) (cong (_·' o) p) (cong (_·' o) q) i j

  m·n≡m·'n : ∀ {A} (m n : FreeMonoid A) → m · n ≡ m ·' n
  m·n≡m·'n ε n = εₗ n
  m·n≡m·'n [ x ] n = refl
  m·n≡m·'n (m · n) o = sym (assoc _ _ _) ∙ cong (m ·_) (m·n≡m·'n n o)
  m·n≡m·'n (εₗ m i) n = isSet→isSet' trunc
    -- (m·n≡m·'n (ε · m) n) expanded
    (sym (assoc _ _ _) ∙ cong (ε ·_) (m·n≡m·'n m n))
    (m·n≡m·'n m n)
    (λ i → εₗ m i · n)
    -- (λ i → εₗ m i ·' n) expanded
    (εₗ (m ·' n))
    i
  m·n≡m·'n (εᵣ m i) n = isSet→isSet' trunc
    -- (m·n≡m·'n (m · ε) n) expanded
    (sym (assoc _ _ _) ∙ cong (m ·_) (εₗ n))
    (m·n≡m·'n m n)
    (λ i → εᵣ m i · n)
    -- (λ i → εᵣ m i ·' n) expanded
    (m·n≡m·'n m n)
    i
  m·n≡m·'n (assoc m n o i) p = isSet→isSet' trunc
    -- (m·n≡m·'n (m · n · o) p) expanded
    (sym (assoc _ _ _) ∙ cong (m ·_) (sym (assoc _ _ _) ∙ cong (n ·_) (m·n≡m·'n o p)))
    -- (m·n≡m·'n ((m · n) · o) p) expanded
    (sym (assoc _ _ _) ∙ cong ((m · n) ·_) (m·n≡m·'n o p))
    (λ i → assoc m n o i · p)
    -- (λ i → assoc m n o i ·' p) expanded
    (assoc m n (o ·' p))
    i
  m·n≡m·'n (trunc m n p q i j) o = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
    (λ i → m·n≡m·'n (p i) o)
    (λ i → m·n≡m·'n (q i) o)
    (λ i → m·n≡m·'n m o)
    (λ i → m·n≡m·'n n o)
    (λ i j → trunc m n p q i j · o)
    -- (λ i j → trunc m n p q i j ·' o) expanded
    (trunc (m ·' o) (n ·' o) (cong (_·' o) p) (cong (_·' o) q))
    i j

module Elim {A} {P : FreeMonoid A → Type}
  (ε* : P ε)
  ([_]* : (x : A) → P [ x ])
  (_·*_ : ∀ {m n} → P m → P n → P (m · n))
  (εₗ* : ∀ {m} (m* : P m)
    → PathP (λ i → P (εₗ m i)) (ε* ·* m*) m*)
  (εᵣ* : ∀ {m} (m* : P m)
    → PathP (λ i → P (εᵣ m i)) (m* ·* ε*) (m*))
  (assoc* : ∀ {m n o} (m* : P m) (n* : P n) (o* : P o)
    → PathP (λ i → P (assoc m n o i)) (m* ·* (n* ·* o*)) ((m* ·* n*) ·* o*))
  (trunc* : ∀ m → isSet (P m))
  where

  f : (m : FreeMonoid A) → P m
  f ε = ε*
  f [ x ] = [ x ]*
  f (m · n) = f m ·* f n
  f (εₗ m i) = εₗ* (f m) i
  f (εᵣ m i) = εᵣ* (f m) i
  f (assoc m n o i) = assoc* (f m) (f n) (f o) i
  f (trunc m n p q i j) = isOfHLevel→isOfHLevelDep 2 trunc* (f m) (f n) (cong f p) (cong f q) (trunc m n p q) i j

module ElimProp {A} {P : FreeMonoid A → Type} (PProp : {m : FreeMonoid A} → isProp (P m))
  (ε* : P ε)
  ([_]* : (x : A) → P [ x ])
  (_·*_ : ∀ {m n} → P m → P n → P (m · n))
  where

  f : (m : FreeMonoid A) → P m
  f = Elim.f ε* [_]* _·*_
    (λ {m} m* → toPathP (PProp (transport (λ i → P (εₗ m i)) (ε* ·* m*)) m*))
    (λ {m} m* → toPathP (PProp (transport (λ i → P (εᵣ m i)) (m* ·* ε*)) m*))
    (λ {m n o} m* n* o* → toPathP (PProp (transport (λ i → P (assoc m n o i)) (m* ·* (n* ·* o*))) ((m* ·* n*) ·* o*)))
    (λ _ → isProp→isSet PProp)

module Rec {A B : Type} (BType : isSet B)
  (ε* : B)
  ([_]* : (x : A) → B)
  (_·*_ : B → B → B)
  (εₗ* : ∀ (x : B) → ε* ·* x ≡ x)
  (εᵣ* : ∀ (x : B) → x ·* ε* ≡ x)
  (assoc* : ∀ (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  where

  f : (m : FreeMonoid A) → B
  f = Elim.f ε* [_]* _·*_ εₗ* εᵣ* assoc* (const BType)

reverse : ∀ {A} → FreeMonoid A → FreeMonoid A
reverse =
  Rec.f trunc ε [_] (flip _·_) εᵣ εₗ (λ m n o → sym (assoc o n m))

reverse-involutive : ∀ {A} (m : FreeMonoid A) → reverse (reverse m) ≡ m
reverse-involutive =
  ElimProp.f
    (λ {m} → trunc (reverse (reverse m)) m)
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)

map : ∀ {A B} → (A → B) → FreeMonoid A → FreeMonoid B
map f = Rec.f trunc ε ([_] ∘ f) _·_ εₗ εᵣ assoc

map-id : ∀ {A} → map (idfun A) ≡ idfun (FreeMonoid A)
map-id = funExt $
  ElimProp.f
    (λ {m} → trunc (map (idfun _) m) m)
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)

map-∘ : ∀ {A B C} (f : B → C) (g : A → B) → map f ∘ map g ≡ map (f ∘ g)
map-∘ f g = funExt $
  ElimProp.f
    (λ {m} → trunc ((map f ∘ map g) m) (map (f ∘ g) m))
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)

join : ∀ {A} → FreeMonoid (FreeMonoid A) → FreeMonoid A
join = Rec.f trunc ε (idfun (FreeMonoid _)) _·_ εₗ εᵣ assoc

map-pure-join : ∀ {A} → join ∘ map [_] ≡ idfun (FreeMonoid A)
map-pure-join = funExt $
  ElimProp.f
    (λ {m} → trunc ((join ∘ map [_]) m) m)
    refl
    (λ _ → refl)
    (λ p q → cong₂ _·_ p q)
