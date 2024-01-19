{-# OPTIONS --cubical #-}

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Foundations.Everything hiding ( empty )
open import Cubical.Foundations.Function using ( idfun; _∘_ )

private
  variable
    A : Type

--------------------------------------------------------------------------------
-- Infinite list

infixr 5 _∷_

data InfList (A : Type) (d : A) : Type where
  [] : InfList A d
  _∷_ : (x : A) (xs : InfList A d) → InfList A d
  ext : [] ≡ d ∷ []

pattern repeat d = [] {d = d}

replicate : ∀ {d} → ℕ → A → InfList A d
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

extN : ∀ {d : A} (n : ℕ) → repeat d ≡ replicate n d
extN {d = d} zero = refl
extN {d = d} (suc n) = ext ∙ cong (d ∷_) (extN n)

-- Example
_ : 1 ∷ 2 ∷ 3 ∷ repeat 0 ≡ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ repeat 0
_ = λ i → 1 ∷ 2 ∷ 3 ∷ extN 3 i

--------------------------------------------------------------------------------
-- Infinite list zipper

InfZipper : (A : Type) (d : A) → Type
InfZipper A d = InfList A d × InfList A d

empty : (d : A) → InfZipper A d
empty d = [] , []

extract : {d : A} → InfZipper A d → A
extract {d = d} (_ , []) = d
extract {d = d} (_ , x ∷ _) = x
extract {d = d} (_ , ext i) = d

left right : {d : A} → InfZipper A d → InfZipper A d
left {d = d} ([] , rs) = [] , d ∷ rs
left {d = d} (x ∷ ls , rs) = ls , x ∷ rs
left {d = d} (ext i , rs) = [] , d ∷ rs
right {d = d} (ls , []) = d ∷ ls , []
right {d = d} (ls , x ∷ rs) = x ∷ ls , rs
right {d = d} (ls , ext i) = d ∷ ls , []

left∘right≡id : {d : A} → left {d = d} ∘ right ≡ idfun _
left∘right≡id i (ls , []) = ls , sym ext i
left∘right≡id i (ls , x ∷ rs) = ls , x ∷ rs
left∘right≡id i (ls , ext j) = ls , ext (~ i ∨ j)

right∘left≡id : {d : A} → right {d = d} ∘ left ≡ idfun _
right∘left≡id i ([] , rs) = sym ext i , rs
right∘left≡id i (x ∷ ls , rs) = x ∷ ls , rs
right∘left≡id i (ext j , rs) = ext (~ i ∨ j) , rs
