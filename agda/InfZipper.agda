{-# OPTIONS --cubical #-}

module InfZipper where

open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Nat.Base using ( _+_ )

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

--------------------------------------------------------------------------------

infixr 5 _∷_

data InfList {A : Type ℓ} (x₀ : A) : Type ℓ where
  [] : InfList x₀
  _∷_ : (x : A) (xs : InfList x₀) → InfList x₀
  ext : [] ≡ x₀ ∷ []
  trunc : isSet (InfList x₀)

pattern repeat x₀ = [] {x₀ = x₀}

--------------------------------------------------------------------------------

module _ {x₀ : A} {y₀ : B} (f : A → B → C) where

  zipWith : InfList x₀ → InfList y₀ → InfList (f x₀ y₀)
  zipWith []       []       = []
  zipWith []       (y ∷ ys) = f x₀ y ∷ zipWith [] ys
  zipWith (x ∷ xs) []       = f x y₀ ∷ zipWith xs []
  zipWith (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith xs ys
  zipWith []       (ext i)  = ext i
  zipWith (ext i)  []       = ext i
  zipWith (ext i)  (y ∷ ys) = f x₀ y ∷ zipWith [] ys
  zipWith (x ∷ xs) (ext i)  = f x y₀ ∷ zipWith xs []
  zipWith (ext i)  (ext j)  = ext (i ∨ j)
  zipWith [] (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zipWith []) q) (cong (zipWith []) q₁) k l
  zipWith (x ∷ xs) (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zipWith (x ∷ xs)) q) (cong (zipWith (x ∷ xs)) q₁) k l
  zipWith (ext i) (trunc ys ys₁ q q₁ k l) =
    trunc _ _ (cong (zipWith (ext i)) q) (cong (zipWith (ext i)) q₁) k l
  zipWith (trunc xs xs₁ p p₁ i j) ys =
    trunc _ _ (cong (flip zipWith ys) p) (cong (flip zipWith ys) p₁) i j

_ : zipWith _+_ (1 ∷ 2 ∷ 3 ∷ repeat 1) (4 ∷ 5 ∷ repeat 6) ≡
    5 ∷ 7 ∷ 9 ∷ repeat 7
_ = refl

--------------------------------------------------------------------------------

InfZipper : {A : Type ℓ} (x₀ : A) → Type ℓ
InfZipper x₀ = InfList x₀ × InfList x₀

module _ {x₀ : A} where

  isSetInfZipper : isSet (InfZipper x₀)
  isSetInfZipper = isSet× trunc trunc

  extract : isSet A → InfZipper x₀ → A
  extract AType (ls , []) = x₀
  extract AType (ls , x ∷ rs) = x
  extract AType (ls , ext i) = x₀
  extract AType (ls , trunc rs rs₁ p q i j) = AType _ _
    (cong (extract AType ∘ (ls ,_)) p)
    (cong (extract AType ∘ (ls ,_)) q)
    i j

  update : (A → A) → InfZipper x₀ → InfZipper x₀
  update f (ls , []) = ls , f x₀ ∷ []
  update f (ls , x ∷ rs) = ls , f x ∷ rs
  update f (ls , ext i) = ls , f x₀ ∷ []
  update f (ls , trunc rs rs₁ p q i j) = isSetInfZipper _ _
    (cong (update f ∘ (ls ,_)) p)
    (cong (update f ∘ (ls ,_)) q)
    i j

  update-id : ∀ xs → update (idfun _) xs ≡ xs
  update-id (ls , []) = cong (ls ,_) (sym ext)
  update-id (ls , y ∷ rs) = refl
  update-id (ls , ext i) j = ls , ext (i ∨ ~ j)
  update-id (ls , trunc rs rs₁ p q i j) = isOfHLevel→isOfHLevelDep 2
    (λ xs → isProp→isSet (isSetInfZipper (update (idfun _) xs) xs))
    _ _
    (cong (update-id ∘ (ls ,_)) p)
    (cong (update-id ∘ (ls ,_)) q)
    (λ i j → ls , trunc rs rs₁ p q i j)
    i j

  left right : InfZipper x₀ → InfZipper x₀
  left ([] , rs) = [] , x₀ ∷ rs
  left (x ∷ ls , rs) = ls , x ∷ rs
  left (ext i , rs) = [] , x₀ ∷ rs
  left (trunc ls ls₁ p q i j , rs) = isSetInfZipper _ _
    (cong (left ∘ (_, rs)) p)
    (cong (left ∘ (_, rs)) q)
    i j
  right (ls , []) = x₀ ∷ ls , []
  right (ls , x ∷ rs) = x ∷ ls , rs
  right (ls , ext i) = x₀ ∷ ls , []
  right (ls , trunc rs rs₁ p q i j) = isSetInfZipper _ _
    (cong (right ∘ (ls ,_)) p)
    (cong (right ∘ (ls ,_)) q)
    i j

  left-right : ∀ xs → right (left xs) ≡ xs
  left-right ([] , rs) = cong (_, rs) (sym ext)
  left-right (x ∷ ls , rs) = refl
  left-right (ext i , rs) j = ext (i ∨ ~ j) , rs
  left-right (trunc ls ls₁ p q i j , rs) = isOfHLevel→isOfHLevelDep 2
    (λ xs → isProp→isSet (isSetInfZipper (right (left xs)) xs))
    _ _
    (cong (left-right ∘ (_, rs)) p)
    (cong (left-right ∘ (_, rs)) q)
    (λ i j → trunc ls ls₁ p q i j , rs)
    i j

  right-left : ∀ xs → left (right xs) ≡ xs
  right-left (ls , []) = cong (ls ,_) (sym ext)
  right-left (ls , x ∷ rs) = refl
  right-left (ls , ext i) j = ls , ext (i ∨ ~ j)
  right-left (ls , trunc rs rs₁ p q i j) = isOfHLevel→isOfHLevelDep 2
    (λ xs → isProp→isSet (isSetInfZipper (left (right xs)) xs))
    _ _
    (cong (right-left ∘ (ls ,_)) p)
    (cong (right-left ∘ (ls ,_)) q)
    (λ i j → ls , trunc rs rs₁ p q i j)
    i j
