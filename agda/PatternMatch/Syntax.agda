{-# OPTIONS --guardedness #-}

module PatternMatch.Syntax where

open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.List as List using ( List; _∷_; [] )
open import Data.List.Relation.Unary.All using ( All; _∷_; [] )
open import Data.Nat using ( ℕ )
open import Data.Vec using ( allFin )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )
open import Relation.Nullary using ( ¬_ )

open import PatternMatch.Utils

private
  variable
    A B : Set

--------------------------------------------------------------------------------

record Ty : Set where
  coinductive
  field
    ∣_∣ᶜ : ℕ -- the number of constructors
  Ctor = Fin ∣_∣ᶜ
  ctors = allFin ∣_∣ᶜ
  field
    args : Ctor → List Ty

open Ty public

private
  variable
    α β : Ty

--------------------------------------------------------------------------------

mutual
  data Val (α : Ty) : Set where
    con : (c : Ctor α) → Vals (args α c) → Val α

  Vals : List Ty → Set
  Vals = All Val

--------------------------------------------------------------------------------

infixr 5 _∣_

mutual
  data Pat (α : Ty) : Set where
    -- Wildcard
    — : Pat α
    -- Constructor pattern
    con : (c : Ctor α) → Pats (args α c) → Pat α
    -- Or pattern
    _∣_ : Pat α → Pat α → Pat α

  Pats : List Ty → Set
  Pats = All Pat

--------------------------------------------------------------------------------

`⊥ : Ty
∣ `⊥ ∣ᶜ = 0
args `⊥ ()

`ℕ : Ty
∣ `ℕ ∣ᶜ = 2
args `ℕ zero = []
args `ℕ (suc zero) = `ℕ ∷ []

`List : Ty → Ty
∣ `List α ∣ᶜ = 2
args (`List α) zero = []
args (`List α) (suc zero) = α ∷ `List α ∷ []

`zero : Val `ℕ
`zero = con zero []

`nil : Val (`List α)
`nil = con zero []

infixr 5 _`∷_
_`∷_ : Val α → Val (`List α) → Val (`List α)
x `∷ xs = con (suc zero) (x ∷ xs ∷ [])

`zeroₚ : Pat `ℕ
`zeroₚ = con zero []

`sucₚ : Pat `ℕ → Pat `ℕ
`sucₚ n = con (suc zero) (n ∷ [])

`nilₚ : Pat (`List α)
`nilₚ = con zero []

infixr 5 _`∷ₚ_
_`∷ₚ_ : Pat α → Pat (`List α) → Pat (`List α)
x `∷ₚ xs = con (suc zero) (x ∷ xs ∷ [])

_ : Pat (`List `ℕ)
_ = `zeroₚ `∷ₚ (`sucₚ `zeroₚ) `∷ₚ (`sucₚ (`sucₚ —)) `∷ₚ —
