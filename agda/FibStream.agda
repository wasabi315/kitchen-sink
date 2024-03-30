{-# OPTIONS --sized-types #-}

module FibStream where

open import Size
open import Codata.Sized.Stream
open import Codata.Sized.Thunk
open import Data.Nat
open import Relation.Binary.PropositionalEquality

private
  variable
    A B C : Set
    i : Size

fibs : Stream ℕ i
fibs = 0 ∷ λ where .force → 1 ∷ λ where .force → zipWith _+_ fibs (tail fibs)

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (2+ n) = fib n + fib (suc n)

lookup-zipWith : ∀ (f : A → B → C) xs ys n
  → f (lookup xs n) (lookup ys n) ≡ lookup (zipWith f xs ys) n
lookup-zipWith f (x ∷ xs) (y ∷ ys) zero = refl
lookup-zipWith f (x ∷ xs) (y ∷ ys) (suc n) = lookup-zipWith f (force xs) (force ys) n

fibs-correct : ∀ n → lookup fibs n ≡ fib n
fibs-correct 0 = refl
fibs-correct 1 = refl
fibs-correct (2+ n) = begin
  lookup (tail (tail fibs)) n              ≡⟨⟩
  lookup (zipWith _+_ fibs (tail fibs)) n  ≡⟨ lookup-zipWith _+_ fibs (tail fibs) n ⟨
  lookup fibs n + lookup (tail fibs) n     ≡⟨⟩
  lookup fibs n + lookup fibs (suc n)      ≡⟨ cong₂ _+_ (fibs-correct n) (fibs-correct (suc n)) ⟩
  fib n + fib (suc n)                      ∎
  where open ≡-Reasoning
