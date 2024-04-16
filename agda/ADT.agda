{-# OPTIONS --guardedness #-}

open import Data.Fin using ( Fin; zero; suc )
open import Data.Nat using ( ℕ; zero; suc )
open import Data.List using ( List; _∷_; [] )
open import Data.Product using ( _×_; _,_ )
open import Data.Unit using ( ⊤; tt )
open import Relation.Nullary using ( ¬_ )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Misc

List→Type : (A → Set) → List A → Set
List→Type P [] = ⊤
List→Type P (x ∷ []) = P x
List→Type P (x ∷ xs) = P x × List→Type P xs

--------------------------------------------------------------------------------

record Ty : Set where
  coinductive
  field
    numv : ℕ -- the number of variants
    args : Fin numv → List Ty

open Ty

private
  variable
    α β : Ty

`⊤ : Ty
numv `⊤ = 1
args `⊤ zero = []

`⊥ : Ty
numv `⊥ = 0
args `⊥ ()

`Bool : Ty
numv `Bool = 2
args `Bool zero = []
args `Bool (suc zero) = []

`ℕ : Ty
numv `ℕ = 2
args `ℕ zero = []
args `ℕ (suc zero) = `ℕ ∷ []

`Pair : Ty → Ty → Ty
numv (`Pair α β) = 1
args (`Pair α β) zero = α ∷ β ∷ []

`List : Ty → Ty
numv (`List α) = 2
args (`List α) zero = []
args (`List α) (suc zero) = α ∷ `List α ∷ []

--------------------------------------------------------------------------------

data Val (α : Ty) : Set where
  con : (v : Fin (numv α)) → List→Type Val (args α v) → Val α

pattern con0 v = con v tt

opaque

  `tt : Val `⊤
  `tt = con0 zero

  `false `true : Val `Bool
  `false = con0 zero
  `true = con0 (suc zero)

  `zero : Val `ℕ
  `zero = con0 zero

  `suc : Val `ℕ → Val `ℕ
  `suc n = con (suc zero) n

  infixr 4 _`,_
  _`,_ : Val α → Val β → Val (`Pair α β)
  x `, y = con zero (x , y)

  `nil : Val (`List α)
  `nil = con0 zero

  infixr 5 _`∷_
  _`∷_ : Val α → Val (`List α) → Val (`List α)
  x `∷ xs = con (suc zero) (x , xs)

¬Val`⊥ : ¬ Val `⊥
¬Val`⊥ (con () _)

--------------------------------------------------------------------------------

data Pat (α : Ty) : Set where
  - : Pat α
  con : (v : Fin (numv α)) → List→Type Pat (args α v) → Pat α

pattern con0 v = con v tt

opaque

  `zeroₚ : Pat `ℕ
  `zeroₚ = con0 zero

  `sucₚ : Pat `ℕ → Pat `ℕ
  `sucₚ n = con (suc zero) n

  `nilₚ : Pat (`List α)
  `nilₚ = con0 zero

  infixr 5 _`∷ₚ_
  _`∷ₚ_ : Pat α → Pat (`List α) → Pat (`List α)
  x `∷ₚ xs = con (suc zero) (x , xs)

_ : Pat (`List `ℕ)
_ = `zeroₚ `∷ₚ (`sucₚ `zeroₚ) `∷ₚ (`sucₚ (`sucₚ -)) `∷ₚ -
