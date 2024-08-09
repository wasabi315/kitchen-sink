-- Ref: https://github.com/pa-ba/calc-graph-comp

{-# OPTIONS --guarded --cubical #-}

module Guarded.CFG where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool using ( Dec→Bool; if_then_else_ )
open import Cubical.Data.Int using ( ℤ; pos; neg; _+_; discreteℤ )
open import Cubical.Data.List using ( List; []; _∷_ )
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Vec using ( Vec; []; _∷_ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Relation.Nullary using ( Dec; yes; no )

open import Guarded.Prims
open import Guarded.Partial

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Differences from the original Code/Codeᵍ:
--   * terminator instructions are separated from other instructions
--   * LABᵍ→ and LABᵍ← are merged into a single label constructor
--   * some higher-inductive cases are added
--   * guarded recursion instead of sized types

infixr 5 _∷_
infixl 4 label-syntax

data CFG (L : Set) (I : Set) (T : ℕ → Set) : Set where
  _∷_ : (x : I) (c : CFG L I T) → CFG L I T
  term : ∀ {n} (t : T n) (ls : Vec L n) → CFG L I T
  -- instructions before/after the label
  label : (c₁ c₂ : L → CFG L I T) → CFG L I T

  ∷-label-comm : (x : I) (c₁ c₂ : L → CFG L I T)
    → x ∷ label c₁ c₂ ≡ label (λ l → x ∷ c₁ l) c₂
  label-discard : (c₁ : CFG L I T) (c₂ : L → CFG L I T)
    → label (λ _ → c₁) c₂ ≡ c₁

label-syntax : ∀ {L I T} (f g : L → CFG L I T) → CFG L I T
label-syntax = label
syntax label-syntax (λ l₁ → c₁) (λ l₂ → c₂) = c₁ label[ l₁ , l₂ ] c₂

data Tree (I : Set) (T : ℕ → Set) : Set where
  _∷_ : (x : I) (t : Tree I T) → Tree I T
  branch : ∀ {n} (t : T n) (ts : Vec (Tree I T) n) → Tree I T
  rec : (t▹ : ▹ Tree I T) → Tree I T

unlabel : ∀ {I T} → CFG (Tree I T) I T → Tree I T
unlabel (x ∷ c) = x ∷ unlabel c
unlabel (term t ls) = branch t ls
unlabel (label c₁ c₂) = unlabel $ c₁ $ fix λ c▹ → unlabel $ c₂ $ rec c▹
unlabel (∷-label-comm x c₁ c₂ i) = x ∷ (unlabel $ c₁ $ fix λ c▹ → unlabel $ c₂ $ rec c▹)
unlabel (label-discard c₁ c₂ i) = unlabel c₁

--------------------------------------------------------------------------------

data Instr : Set where
  push : ℤ → Instr
  add store load pop : Instr

-- Terminator instructions indexed by the number of labels they take as operands
data Term : ℕ → Set where
  ret : Term 0
  jpz : Term 2
  jmp : Term 1

pattern retᵍ = term ret []
pattern jpzᵍ l1 l2 = term jpz (l1 ∷ l2 ∷ [])
pattern jmpᵍ l = term jmp (l ∷ [])
pattern retᵗ = branch ret []
pattern jpzᵗ t1 t2 = branch jpz (t1 ∷ t2 ∷ [])
pattern jmpᵗ t = branch jmp (t ∷ [])

--------------------------------------------------------------------------------

infixl 5 _`+_

data Expr : Set where
  val : ℤ → Expr
  _`+_ : Expr → Expr → Expr
  put : Expr → Expr → Expr
  get : Expr
  while : Expr → Expr → Expr

eval : Expr → ℤ → Part (ℤ × ℤ)
eval (val n) s = return (n , s)
eval (x `+ y) s = do
  m , s₁ ← eval x s
  n , s₂ ← eval y s₁
  return (m + n , s₂)
eval (put x y) s = do
  n , _ ← eval x s
  eval y n
eval get s = return (s , s)
eval (while x y) = fix λ f▹ s → do
  n , s₁ ← eval x s
  if Dec→Bool (discreteℤ n (pos 0))
    then return (pos 0 , s₁)
    else do
      _ , s₂ ← eval y s₁
      later λ α → f▹ α s₂

--------------------------------------------------------------------------------

execᵗ : Tree Instr Term → (List ℤ × ℤ) → Part (List ℤ × ℤ)
execᵗ (push n ∷ t) (ss , s) = execᵗ t (n ∷ ss , s)
execᵗ (add ∷ t) (m ∷ n ∷ ss , s) = execᵗ t ((n + m) ∷ ss , s)
execᵗ (store ∷ t) (n ∷ ss , _) = execᵗ t (ss , n)
execᵗ (load ∷ t) (ss , s) = execᵗ t (s ∷ ss , s)
execᵗ (pop ∷ t) (_ ∷ ss , s) = execᵗ t (ss , s)
execᵗ retᵗ conf = return conf
execᵗ (jpzᵗ t₁ t₂) (n ∷ ss , s) =
  if Dec→Bool (discreteℤ n (pos 0))
    then execᵗ t₁ (pos 0 ∷ ss , s)
    else execᵗ t₂ (ss , s)
execᵗ (jmpᵗ t) conf = execᵗ t conf
execᵗ (rec t▹) conf = later λ α → execᵗ (t▹ α) conf
execᵗ _ _ = return ([] , pos 0)

compᵗ : Expr → Tree Instr Term → Tree Instr Term
compᵗ (val n) t = push n ∷ t
compᵗ (x `+ y) t = compᵗ x $ compᵗ y $ add ∷ t
compᵗ (put x y) t = compᵗ x $ store ∷ compᵗ y t
compᵗ get t = load ∷ t
compᵗ (while x y) t = fix λ t▹ →
  compᵗ x $ jpzᵗ t $ compᵗ y $ pop ∷ rec t▹

compileᵗ : Expr → Tree Instr Term
compileᵗ e = compᵗ e retᵗ

expr : Expr
expr = put (val (pos 10)) (while get (put (get `+ val (neg 1)) get))

--------------------------------------------------------------------------------

compᵍ : ∀ {L} → Expr → CFG L Instr Term → CFG L Instr Term
compᵍ (val n) c = push n ∷ c
compᵍ (x `+ y) c = compᵍ x $ compᵍ y (add ∷ c)
compᵍ (put x y) c = compᵍ x $ store ∷ compᵍ y c
compᵍ get c = load ∷ c
compᵍ (while x y) c =
    jmpᵍ l₁
  label[ l₁ , l₁ ]
    (compᵍ x
    (jpzᵍ l₃ l₂)
  label[ l₂ , _ ]
    compᵍ y
    (pop ∷
    jmpᵍ l₁)
  label[ l₃ , _ ]
    c)

compileᵍ : ∀ {L} → Expr → CFG L Instr Term
compileᵍ e = compᵍ e retᵍ

execᵍ : (∀ {L} → CFG L Instr Term) → (List ℤ × ℤ) → Part (List ℤ × ℤ)
execᵍ c conf = execᵗ (unlabel c) conf

--------------------------------------------------------------------------------

{-
        |                   +----------<-----------+
        v        +---->---+ |      +--->----+      |
    .---------.  |  . l₁ -+-+---.  |  . l₂ -+---.  |
    | push 10 |  |  | load      |  |  | load    |  |
    | store   |  ^  | jpz l₃ l₂ |  ^  | push -1 |  |
    | jmp l₁  |  |  '-----+--+--'  |  | add     |  |
    '----+----'  |        v  +-->--+  | store   |  ^
         +--->---+  . l₂ -+-----.     | load    |  |
                    | tret      |     | pop     |  |
                    '-----------'     | jmp l₁  |  |
                                      '----+----'  |
                                           +--->---+
-}

cfg : ∀ {L} → CFG L Instr Term
cfg =
    push (pos 10) ∷
    store ∷
    jmpᵍ l₁
  label[ l₁ , l₁ ]
    (load ∷
    jpzᵍ l₃ l₂
  label[ l₂ , _ ]
    load ∷
    push (neg 1) ∷
    add ∷
    store ∷
    load ∷
    pop ∷
    jmpᵍ l₁
  label[ l₃ , _ ]
    retᵍ)

tree : Tree Instr Term
tree =
  push (pos 10) ∷
  store ∷
  jmpᵗ (fix λ c▹ →
    load ∷
    jpzᵗ retᵗ (
      load ∷
      push (neg 1) ∷
      add ∷
      store ∷
      load ∷
      pop ∷
      jmpᵗ (rec c▹)))

_ : unlabel cfg ≡ tree
_ = refl
