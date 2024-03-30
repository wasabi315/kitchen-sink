{-# OPTIONS --cubical --safe #-}

module FreeMonoid where

open import Level using ( Level )
open import Cubical.Algebra.Monoid
open import Cubical.Data.List.Base using ( List; []; _∷_; _++_; foldr )
open import Cubical.Data.List.Properties using ( isOfHLevelList; ++-unit-r; ++-assoc )
open import Cubical.Foundations.Everything hiding ( assoc )
open import Cubical.Foundations.HLevels

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

infixr 5 _·_ _·'_

data FreeMonoid (A : Type ℓ) : Type ℓ where
  ε : FreeMonoid A
  [_] : (x : A) → FreeMonoid A
  _·_ : (m n : FreeMonoid A) → FreeMonoid A

  εₗ : ∀ m → ε · m ≡ m
  εᵣ : ∀ m → m · ε ≡ m
  assoc : ∀ m n o → m · (n · o) ≡ (m · n) · o
  trunc : isSet (FreeMonoid A)

freeIsMonoid : ∀ (A : Type ℓ) → IsMonoid ε _·_
freeIsMonoid A = makeIsMonoid (trunc {A = A}) assoc εᵣ εₗ

freeMonoid : ∀ (A : Type ℓ) → Monoid _
freeMonoid A = monoid (FreeMonoid A) ε _·_ (freeIsMonoid A)

--------------------------------------------------------------------------------

module Elim {P : FreeMonoid A → Type ℓ'}
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
  f (trunc m n p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc* (f m) (f n) (cong f p) (cong f q) (trunc m n p q) i j

module ElimProp {P : FreeMonoid A → Type ℓ'} (PProp : ∀ {m} → isProp (P m))
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

module Rec (BType : isSet B)
  (ε* : B)
  ([_]* : (x : A) → B)
  (_·*_ : B → B → B)
  (εₗ* : ∀ (x : B) → ε* ·* x ≡ x)
  (εᵣ* : ∀ (x : B) → x ·* ε* ≡ x)
  (assoc* : ∀ (x y z : B) → x ·* (y ·* z) ≡ (x ·* y) ·* z)
  where

  f : (m : FreeMonoid A) → B
  f = Elim.f ε* [_]* _·*_ εₗ* εᵣ* assoc* (const BType)

--------------------------------------------------------------------------------

module _ {M : Monoid ℓ'} (f : A → ⟨ M ⟩) where
  open MonoidStr (str M) renaming ( ε to ε*; _·_ to _·*_ )

  hom : FreeMonoid A → ⟨ M ⟩
  hom = Rec.f is-set ε* f _·*_ ·IdL ·IdR ·Assoc

  homIsHom : IsMonoidHom (str (freeMonoid A)) hom (str M)
  homIsHom = monoidequiv refl (λ _ _ → refl)

  homHom : MonoidHom (freeMonoid A) M
  homHom = hom , homIsHom

--------------------------------------------------------------------------------

mutual

  -- slow append: (m ·' n) appends n next to the rightmost node of m
  _·'_ : FreeMonoid A → FreeMonoid A → FreeMonoid A
  ε ·' n = n
  [ x ] ·' n = [ x ] · n
  (m · n) ·' o = m · (n ·' o)
  εₗ m i ·' n = εₗ (m ·' n) i
  εᵣ m i ·' n = m·n≡m·'n m n i
  assoc m n o i ·' p = assoc m n (o ·' p) i
  trunc m n p q i j ·' o =
    trunc (m ·' o) (n ·' o) (cong (_·' o) p) (cong (_·' o) q) i j

  m·n≡m·'n : (m n : FreeMonoid A) → m · n ≡ m ·' n
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

--------------------------------------------------------------------------------

module _ {A : Type ℓ} (ASet : isSet A) where

  FreeMonoid→List : FreeMonoid A → List A
  FreeMonoid→List =
    Rec.f
      (isOfHLevelList 0 ASet)
      []
      (_∷ [])
      _++_
      (λ _ → refl)
      ++-unit-r
      (λ xs ys zs → sym (++-assoc xs ys zs))

  List→FreeMonoid : List A → FreeMonoid A
  List→FreeMonoid = foldr (λ x xs → [ x ] · xs) ε

  sct : section FreeMonoid→List List→FreeMonoid
  sct [] = refl
  sct (x ∷ xs) i = x ∷ sct xs i

  List→FreeMonoid-++ : ∀ (xs ys : List A)
    → List→FreeMonoid (xs ++ ys) ≡ List→FreeMonoid xs · List→FreeMonoid ys
  List→FreeMonoid-++ [] ys = sym (εₗ (List→FreeMonoid ys))
  List→FreeMonoid-++ (x ∷ xs) ys =
      [ x ] · List→FreeMonoid (xs ++ ys)
    ≡⟨ congS ([ x ] ·_) (List→FreeMonoid-++ xs ys) ⟩
      [ x ] · (List→FreeMonoid xs · List→FreeMonoid ys)
    ≡⟨ assoc [ x ] (List→FreeMonoid xs) (List→FreeMonoid ys) ⟩
      ([ x ] · List→FreeMonoid xs) · List→FreeMonoid ys
    ∎

  rtr : retract FreeMonoid→List List→FreeMonoid
  rtr =
    ElimProp.f
      (λ {m} → trunc (List→FreeMonoid (FreeMonoid→List m)) m)
      refl
      (λ x → εᵣ [ x ])
      (λ {m} {n} p q →
          List→FreeMonoid (FreeMonoid→List (m · n))
        ≡⟨⟩
          List→FreeMonoid (FreeMonoid→List m ++ FreeMonoid→List n)
        ≡⟨ List→FreeMonoid-++ (FreeMonoid→List m) (FreeMonoid→List n) ⟩
          List→FreeMonoid (FreeMonoid→List m) · List→FreeMonoid (FreeMonoid→List n)
        ≡⟨ cong₂ _·_ p q ⟩
          m · n
        ∎)

  FreeMonoidIsoList : Iso (FreeMonoid A) (List A)
  FreeMonoidIsoList = iso FreeMonoid→List List→FreeMonoid sct rtr

  FreeMonoid≃List : FreeMonoid A ≃ List A
  FreeMonoid≃List = isoToEquiv FreeMonoidIsoList

  FreeMonoid≡List : FreeMonoid A ≡ List A
  FreeMonoid≡List = isoToPath FreeMonoidIsoList
