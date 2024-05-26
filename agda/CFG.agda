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
infixl 4 label→-syntax
infixl 3 label↔-syntax

data CFG (L : Set) (I : Set) (T : ℕ → Set) : Set where
  _∷_ : (i : I) (c : CFG L I T) → CFG L I T
  term : ∀ {n} (t : T n) (ls : Vec L n) → CFG L I T
  -- instructions before/after the label
  label : (c₁ c₂ : L → CFG L I T) → CFG L I T

  ∷-label-comm : (x : I) (c₁ c₂ : L → CFG L I T)
    → x ∷ label c₁ c₂ ≡ label (λ l → x ∷ c₁ l) c₂
  label-discard : (c₁ : CFG L I T) (c₂ : L → CFG L I T)
    → label (λ _ → c₁) c₂ ≡ c₁

data Tree (I : Set) (T : ℕ → Set) : Set where
  _∷_ : I → Tree I T → Tree I T
  branch : ∀ {n} → T n → Vec (Tree I T) n → Tree I T
  rec : ▹ Tree I T → Tree I T

unlabel : ∀ {I T} → CFG (Tree I T) I T → Tree I T
unlabel (x ∷ c) = x ∷ unlabel c
unlabel (term t ls) = branch t ls
unlabel (label c₁ c₂) = unlabel $ c₁ $ fix λ c▹ → unlabel $ c₂ $ rec c▹
unlabel (∷-label-comm x c₁ c₂ i) = x ∷ (unlabel $ c₁ $ fix λ c▹ → unlabel $ c₂ $ rec c▹)
unlabel (label-discard c₁ c₂ i) = unlabel c₁

--------------------------------------------------------------------------------

label↔-syntax : ∀ {L I T} (f g : L → CFG L I T) → CFG L I T
label↔-syntax = label
syntax label↔-syntax (λ l₁ → c₁) (λ l₂ → c₂) = c₁ label[ l₁ , l₂ ] c₂

label→-syntax : ∀ {L I T} (c₁ : L → CFG L I T) (c₂ : CFG L I T) → CFG L I T
label→-syntax c₁ c₂ = label c₁ (λ _ → c₂)
syntax label→-syntax (λ l → c₁) c₂ = c₁ label[ l ] c₂

--------------------------------------------------------------------------------

data Instr : Set where
  push : ℤ → Instr
  add store load pop : Instr

-- Terminator instructions indexed by the number of labels they take as operands
data Term : ℕ → Set where
  ret : Term 0
  jpz : Term 2
  jmp : Term 1

pattern gret = term ret []
pattern gjpz l1 l2 = term jpz (l1 ∷ l2 ∷ [])
pattern gjmp l = term jmp (l ∷ [])
pattern tret = branch ret []
pattern tjpz t1 t2 = branch jpz (t1 ∷ t2 ∷ [])
pattern tjmp t = branch jmp (t ∷ [])

{-
        |                   +----------<-----------+
        v        +---->---+ |      +--->----+      |
    .---------.  |  . l1 -+-+---.  |  . l2 -+---.  |
    | push 10 |  |  | load      |  |  | load    |  |
    | store   |  ^  | jpz l3 l2 |  ^  | push -1 |  |
    | jmp l1  |  |  '-----+--+--'  |  | add     |  |
    '----+----'  |        v  +-->--+  | store   |  ^
         +--->---+  . l3 -+-----.     | load    |  |
                    | tret      |     | pop     |  |
                    '-----------'     | jmp l1  |  |
                                      '----+----'  |
                                           +--->---+
-}

cfg : ∀ {L} → CFG L Instr Term
cfg =
    push (pos 10) ∷
    store ∷
    gjmp l1
  label[ l1 , l1' ]
    load ∷
    gjpz l3 l2
  label[ l2 ]
    load ∷
    push (neg 1) ∷
    add ∷
    store ∷
    load ∷
    pop ∷
    gjmp l1'
  label[ l3 ]
    gret

tree : Tree Instr Term
tree =
  push (pos 10) ∷
  store ∷
  tjmp (fix λ c▹ →
    load ∷
    tjpz tret (
      load ∷
      push (neg 1) ∷
      add ∷
      store ∷
      load ∷
      pop ∷
      tjmp (rec c▹)))

_ : unlabel cfg ≡ tree
_ = refl
