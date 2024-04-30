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
    αs βs : List Ty

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

mutual
  synth : Pat α → Val α
  synth — = inh _
  synth (con c ps) = con c (synth* ps)
  synth (p ∣ q) = synth p

  synth* : Pat* αs → Val* αs
  synth* [] = []
  synth* (p ∷ ps) = synth p ∷ synth* ps

--------------------------------------------------------------------------------

mutual
  only : Val α → Pat α
  only (con c vs) = con c (only* vs)

  only* : Val* αs → Pat* αs
  only* [] = []
  only* (v ∷ vs) = only v ∷ only* vs

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

-- Can be both Val and Pat
pattern `zero = con zero []
pattern `suc n = con (suc zero) (n ∷ [])

pattern _`,_ x y = con zero (x ∷ y ∷ [])
infixr 4 _`,_

pattern `[] = con zero []
pattern _`∷_ x xs = con (suc zero) (x ∷ xs ∷ [])
infixr 5 _`∷_

exVal : Val (`List `ℕ)
exVal = `zero `∷ `suc `zero `∷ `suc (`suc `zero) `∷ `[]

exPat : Pat (`List `ℕ)
exPat = `zero `∷ (`suc `zero) `∷ (`suc (`suc —)) `∷ —
