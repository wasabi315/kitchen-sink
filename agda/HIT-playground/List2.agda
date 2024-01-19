{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Nat
open import Cubical.Data.List using ( List; []; _∷_ )
open import Cubical.Data.List.Dependent using ( ListP; []; _∷_ )

AllZero : List ℕ → Type₀
AllZero = ListP {A = ℕ} (_≡ 0)

data Foo : List ℕ → List ℕ → Type₀ where
  doneₗ : ∀ {ns} → AllZero ns → Foo [] ns
  doneᵣ : ∀ {ns} → AllZero ns → Foo ns []
  _∷_ : ∀ x {xs ys} → Foo xs ys → Foo (x ∷ xs) (x ∷ ys)

Listℕ₀ : Type₀
Listℕ₀ = List ℕ / Foo

_ :  _≡_ {A = Listℕ₀} [ 1 ∷ 2 ∷ 3 ∷ [] ] [ 1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ [] ]
_ = eq/
  (1 ∷ 2 ∷ 3 ∷ [])
  (1 ∷ 2 ∷ 3 ∷ 0 ∷ 0 ∷ [])
  (1 ∷ 2 ∷ 3 ∷ doneₗ (refl ∷ refl ∷ []))

record State : Type₀ where
  field
    left : Listℕ₀
    current : ℕ
    right : Listℕ₀
