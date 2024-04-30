{-# OPTIONS --guardedness #-}

module PatternMatch.Pattern where

open import Data.Fin using ( Fin; zero; suc )
open import Data.List as List using ( List; _∷_; [] )
open import Data.List.Relation.Unary.All using ( All; _∷_; [] )
open import Data.Nat using ( ℕ )
open import Data.Vec using ( allFin )

--------------------------------------------------------------------------------

mutual
  record Ty : Set where
    coinductive
    field
      numCon : ℕ
    Con = Fin numCon
    allCon = allFin numCon

    field
      args : Con → List Ty
      inhCon : Con
      inhArgs : Val* (args inhCon)

  data Val (α : Ty) : Set where
    con : (c : Ty.Con α) → Val* (Ty.args α c) → Val α

  Val* : List Ty → Set
  Val* = All Val

open Ty public

-- There is always at least one inhabitant
inh : ∀ α → Val α
inh α = con (inhCon α) (inhArgs α)

private
  variable
    α β : Ty

--------------------------------------------------------------------------------

infixr 5 _∣_

mutual
  data Pat (α : Ty) : Set where
    -- Wildcard
    — : Pat α
    -- Constructor pattern
    con : (c : Con α) → Pat* (args α c) → Pat α
    -- Or pattern
    _∣_ : Pat α → Pat α → Pat α

  Pat* : List Ty → Set
  Pat* = All Pat

--------------------------------------------------------------------------------

`ℕ : Ty
numCon `ℕ = 2
args `ℕ zero = []
args `ℕ (suc zero) = `ℕ ∷ []
inhCon `ℕ = zero
inhArgs `ℕ = []

_`×_ : Ty → Ty → Ty
numCon (α `× β) = 1
args (α `× β) zero = α ∷ β ∷ []
inhCon (α `× β) = zero
inhArgs (α `× β) = inh α ∷ inh β ∷ []

`List : Ty → Ty
numCon (`List α) = 2
args (`List α) zero = []
args (`List α) (suc zero) = α ∷ `List α ∷ []
inhCon (`List α) = zero
inhArgs (`List α) = []

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
