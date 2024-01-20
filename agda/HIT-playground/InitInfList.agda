{-# OPTIONS --cubical #-}

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Foundations.Everything hiding ( empty )
open import Cubical.Foundations.Function using ( idfun; _∘_ )

private
  variable
    A : Type

--------------------------------------------------------------------------------
-- "Initialized" infinite list

infixr 5 _∷_

data InitInfList (A : Type) (z : A) : Type where
  [] : InitInfList A z
  _∷_ : (x : A) (xs : InitInfList A z) → InitInfList A z
  ext : [] ≡ z ∷ []
  trunc : isSet (InitInfList A z)

pattern repeat z = [] {z = z}

replicate : ∀ {z} → ℕ → A → InitInfList A z
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

extN : ∀ {z : A} (n : ℕ) → repeat z ≡ replicate n z
extN {z = z} zero = refl
extN {z = z} (suc n) = ext ∙ cong (z ∷_) (extN n)

-- Example
_ : 1 ∷ 2 ∷ 3 ∷ repeat 0 ≡ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ repeat 0
_ = λ i → 1 ∷ 2 ∷ 3 ∷ extN 3 i

--------------------------------------------------------------------------------
-- Initialized infinite list zipper

InitInfZipper : (A : Type) (z : A) → Type
InitInfZipper A z = InitInfList A z × InitInfList A z

isSetInitInfZipper : {z : A} → isSet (InitInfZipper A z)
isSetInitInfZipper = isSet× trunc trunc

empty : (z : A) → InitInfZipper A z
empty z = [] , []

extract : {z : A} → isSet A → InitInfZipper A z → A
extract {z = z} AType (_ , []) = z
extract {z = z} AType (_ , x ∷ _) = x
extract {z = z} AType (_ , ext i) = z
extract {z = z} AType (ls , trunc xs ys p q i j) =
  isSet→isSet' AType
    (λ i → extract AType (ls , p i))
    (λ i → extract AType (ls , q i))
    (λ i → extract AType (ls , xs))
    (λ i → extract AType (ls , ys))
    i j

left right : {z : A} → InitInfZipper A z → InitInfZipper A z
left {z = z} ([] , rs) = [] , z ∷ rs
left {z = z} (x ∷ ls , rs) = ls , x ∷ rs
left {z = z} (ext i , rs) = [] , z ∷ rs
left {z = z} (trunc ls ls₁ p q i j , rs) =
  isSet→isSet' isSetInitInfZipper
    (λ i → left (p i , rs))
    (λ i → left (q i , rs))
    (λ i → left (ls , rs))
    (λ i → left (ls₁ , rs))
    i j
right {z = z} (ls , []) = z ∷ ls , []
right {z = z} (ls , x ∷ rs) = x ∷ ls , rs
right {z = z} (ls , ext i) = z ∷ ls , []
right {z = z} (ls , trunc rs rs₁ p q i j) =
  isSet→isSet' isSetInitInfZipper
    (λ i → right (ls , p i))
    (λ i → right (ls , q i))
    (λ i → right (ls , rs))
    (λ i → right (ls , rs₁))
    i j

left∘right≡id : {z : A} (xs : InitInfZipper A z) → (left ∘ right) xs ≡ xs
left∘right≡id (ls , []) i = ls , sym ext i
left∘right≡id (ls , x ∷ rs) i = ls , x ∷ rs
left∘right≡id (ls , ext j) i = ls , ext (~ i ∨ j)
left∘right≡id (ls , trunc rs rs₁ p q i j) =
  isGroupoid→isGroupoid' (isSet→isGroupoid isSetInitInfZipper)
    (λ i → left∘right≡id (ls , p i))
    (λ i → left∘right≡id (ls , q i))
    (λ i → left∘right≡id (ls , rs))
    (λ i → left∘right≡id (ls , rs₁))
    (λ i j → (left ∘ right) (ls , trunc rs rs₁ p q i j))
    (λ i j → ls , trunc rs rs₁ p q i j)
    i j

right∘left≡id : {z : A} (xs : InitInfZipper A z) → (right ∘ left) xs ≡ xs
right∘left≡id ([] , rs) i = sym ext i , rs
right∘left≡id (x ∷ ls , rs) i = x ∷ ls , rs
right∘left≡id (ext j , rs) i = ext (~ i ∨ j) , rs
right∘left≡id (trunc ls ls₁ p q i j , rs) =
  isGroupoid→isGroupoid' (isSet→isGroupoid isSetInitInfZipper)
    (λ i → right∘left≡id (p i , rs))
    (λ i → right∘left≡id (q i , rs))
    (λ i → right∘left≡id (ls , rs))
    (λ i → right∘left≡id (ls₁ , rs))
    (λ i j → (right ∘ left) (trunc ls ls₁ p q i j , rs))
    (λ i j → trunc ls ls₁ p q i j , rs)
    i j
