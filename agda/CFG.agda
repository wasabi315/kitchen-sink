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
  _label_ :
      (L → CFG L I T) → -- instructions before the label
      (L → CFG L I T) → -- instructions after the label
      CFG L I T
  ∷-label-comm : (x : I) (f g : L → CFG L I T)
    → x ∷ f label g ≡ (λ l → x ∷ f l) label g

data Tree (I : Set) (T : ℕ → Set) : Set where
  _∷_ : I → Tree I T → Tree I T
  branch : ∀ {n} → T n → Vec (Tree I T) n → Tree I T
  rec : ▹ Tree I T → Tree I T

unlabel : {I : Set} {T : ℕ → Set} → CFG (Tree I T) I T → Tree I T
unlabel (x ∷ c) = x ∷ unlabel c
unlabel (term t ls) = branch t ls
unlabel (f label g) = unlabel $ f $ fix λ c▹ → unlabel $ g $ rec c▹
unlabel (∷-label-comm x f g i) = x ∷ unlabel (f (fix λ c▹ → unlabel (g (rec c▹))))

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
                            +----------<-----------+
                 +---->---+ |      +--->----+      |
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
    gjmp
  label λ l1 →
  (λ l3 →
    load ∷
    (gjpz l3)
  label λ l2 →
    load ∷
    push (neg 1) ∷
    add ∷
    store ∷
    load ∷
    pop ∷
    gjmp l1)
  label λ l3 →
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
