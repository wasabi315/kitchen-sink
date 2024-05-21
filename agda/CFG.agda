-- Ref: https://github.com/pa-ba/calc-graph-comp

{-# OPTIONS --guarded --cubical #-}

module CFG where

open import Cubical.Foundations.Everything
open import Cubical.Data.Int using ( ℤ; pos; neg )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( Vec; []; _∷_ )
open import Cubical.Data.Sigma using ( _×_; _,_ )

open import LaterPrims

--------------------------------------------------------------------------------

infixr 5 _∷_
infix 6 _label_

data CFG (L : Set) (I : Set) (T : ℕ → Set) : Set where
  _∷_ : I → CFG L I T → CFG L I T
  term : ∀ {n} → T n → Vec L n → CFG L I T
  _label_ : (L → CFG L I T) → (L → CFG L I T) → CFG L I T

data Tree (I : Set) (T : ℕ → Set) : Set where
  _∷_ : I → Tree I T → Tree I T
  branch : ∀ {n} → T n → Vec (Tree I T) n → Tree I T
  rec : ▹ Tree I T → Tree I T

unlabel : {I : Set} {T : ℕ → Set} → CFG (Tree I T) I T → Tree I T
unlabel (x ∷ c) = x ∷ unlabel c
unlabel (term t ls) = branch t ls
unlabel (f label g) = unlabel $ f $ fix λ c▹ → unlabel $ g $ rec c▹

--------------------------------------------------------------------------------

data Instr : Set where
  push : ℤ → Instr
  add store load pop : Instr

-- Terminator instructions
data Term : ℕ → Set where
  ret : Term 0
  jpz : Term 2
  jmp : Term 1

pattern tret = term ret []
pattern tjpz l1 l2 = term jpz (l1 ∷ l2 ∷ [])
pattern tjmp l = term jmp (l ∷ [])

cfg : ∀ {L} → CFG L Instr Term
cfg =
    push (pos 10) ∷
    store ∷
    tjmp
  label λ l1 →
  (λ l3 →
    load ∷
    (tjpz l3)
  label λ l2 →
    load ∷
    push (neg 1) ∷
    add ∷
    store ∷
    load ∷
    pop ∷
    tjmp l1)
  label λ l3 →
    tret
