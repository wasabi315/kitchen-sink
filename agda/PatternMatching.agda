{-# OPTIONS --guardedness #-}

open import Data.Bool using ( T; _∧_; _∨_; not )
open import Data.Empty using ( ⊥-elim )
open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.List using ( List; _∷_; []; map; _++_ )
open import Data.List.Relation.Unary.Any using ( Any; any?; here; there )
open import Data.Nat using ( ℕ; zero; suc; _≡ᵇ_ )
open import Data.Product using ( _,_; uncurry )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary renaming ( map′ to mapDec )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

private
  variable
    A B : Set

--------------------------------------------------------------------------------
-- Misc

record Zero (n : ℕ) : Set where
  field
    isZero : T (n ≡ᵇ zero)

instance
  zeroZero : Zero zero
  zeroZero = _

--------------------------------------------------------------------------------

record Ty : Set where
  coinductive
  field ∣_∣ᶜ : ℕ -- the number of constructors
  ctor = Fin ∣_∣ᶜ
  field args : Fin ∣_∣ᶜ → List Ty

open Ty

private
  variable
    α β : Ty
    αs βs : List Ty

--------------------------------------------------------------------------------

mutual

  data Val (α : Ty) : Set where
    con : (c : ctor α) → Vals (args α c) → Val α

  data Vals : List Ty → Set where
    [] : Vals []
    _∷_ : Val α → Vals αs → Vals (α ∷ αs)

infixr 5 _∷_

pattern [_] v = v ∷ []
pattern con0 v = con v []

--------------------------------------------------------------------------------

infixr 5 _∣_

mutual

  data Pat (α : Ty) : Set where
    -- Wildcard
    - : Pat α
    -- Constructor pattern
    con : (c : ctor α) → Pats (args α c) → Pat α
    -- Or pattern
    _∣_ : Pat α → Pat α → Pat α

  data Pats : List Ty → Set where
    [] : Pats []
    _∷_ : Pat α → Pats αs → Pats (α ∷ αs)

pattern [_] v = v ∷ []
pattern con0 v = con v []

infixr 5 _++ₚ_
_++ₚ_ : Pats αs → Pats βs → Pats (αs ++ βs)
[] ++ₚ qs = qs
(p ∷ ps) ++ₚ qs = p ∷ ps ++ₚ qs

-* : Pats αs
-* {[]} = []
-* {α ∷ αs} = - ∷ -* {αs}

PatMat : List Ty → Set
PatMat α = List (Pats α)

first-col : PatMat (α ∷ αs) → List (Pat α)
first-col [] = []
first-col ((p ∷ _) ∷ pss) = p ∷ first-col pss

--------------------------------------------------------------------------------

infix 4 _≼_ _≼*_ ≼**-aux _≼?_ _≼*?_ _≼**?_

mutual

  data _≼_ {α} : Pat α → Val α → Set where
    - : ∀ {v} → - ≼ v
    ∣₁ : ∀ {p q v} → p ≼ v → p ∣ q ≼ v
    ∣₂ : ∀ {p q v} → q ≼ v → p ∣ q ≼ v
    con : ∀ (c : ctor α) {ps : Pats (args α c)} {vs : Vals (args α c)}
      → ps ≼* vs
      → con c ps ≼ con c vs

  data _≼*_ : Pats αs → Vals αs → Set where
    [] : [] ≼* []
    _∷_ : ∀ {p : Pat α} {ps : Pats αs} {v vs}
      → p ≼ v
      → ps ≼* vs
      → p ∷ ps ≼* v ∷ vs

pattern [_] v = v ∷ []

data ≼**-aux (vs : Vals αs) : PatMat αs → Set where
  success : ∀ {ps pss}
    → ps ≼* vs
    → ≼**-aux vs (ps ∷ pss)
  fail : ∀ {ps pss}
    → ¬ ps ≼* vs
    → ≼**-aux vs pss
    → ≼**-aux vs (ps ∷ pss)

syntax ≼**-aux vs ps = ps ≼** vs

mutual

  _≼?_ : (p : Pat α) (v : Val α) → Dec (p ≼ v)
  - ≼? v = yes -
  con c ps ≼? con c' vs with c ≟ c'
  ... | no ¬c≡c' = no λ { (con .c _) → ¬c≡c' refl }
  ... | yes refl = mapDec (con c) (λ { (con .c ps≼vs) → ps≼vs }) (ps ≼*? vs)
  p ∣ q ≼? v =
    mapDec
      (λ { (inj₁ p≼v) → ∣₁ p≼v
         ; (inj₂ q≼v) → ∣₂ q≼v })
      (λ { (∣₁ p≼v) → inj₁ p≼v
         ; (∣₂ q≼v) → inj₂ q≼v })
      (p ≼? v ⊎-dec q ≼? v)

  _≼*?_ : (ps : Pats αs) (vs : Vals αs) → Dec (ps ≼* vs)
  [] ≼*? [] = yes []
  p ∷ ps ≼*? v ∷ vs =
    mapDec
      (uncurry _∷_)
      (λ { (p≼v ∷ ps≼vs) → p≼v , ps≼vs })
      (p ≼? v ×-dec ps ≼*? vs)

_≼**?_ : (pss : PatMat αs) (vs : Vals αs) → Dec (pss ≼** vs)
[] ≼**? vs = no λ ()
does (ps ∷ pss ≼**? vs) = does (ps ≼*? vs) ∨ does (pss ≼**? vs)
proof (ps ∷ pss ≼**? vs) with ps ≼*? vs | pss ≼**? vs
... | yes ps≼vs | _ = ofʸ (success ps≼vs)
... | no ¬ps≼vs | yes pss≼vs = ofʸ (fail ¬ps≼vs pss≼vs)
... | no ¬ps≼vs | no ¬pss≼vs =
      ofⁿ λ where
        (success ps≼vs) → ⊥-elim (¬ps≼vs ps≼vs)
        (fail _ pss≼vs) → ⊥-elim (¬pss≼vs pss≼vs)

match : (v : Val α) (ps : List (Pat α)) → Dec (Any (_≼ v) ps)
match v = any? (_≼? v)

--------------------------------------------------------------------------------

infix 4 _,_

record _Useful_ (ps : Pats αs) (pss : PatMat αs) : Set where
  constructor _,_
  field
    {vs} : Vals αs
    ev₁ : ps ≼* vs
    ev₂ : ¬ pss ≼** vs

specialize : (c : ctor α) → PatMat (α ∷ αs) → PatMat (args α c ++ αs)
specialize c [] = []
specialize c ((- ∷ ps) ∷ pss) = (-* ++ₚ ps) ∷ specialize c pss
specialize c ((con c' ps ∷ qs) ∷ pss) with c ≟ c'
... | yes refl = (ps ++ₚ qs) ∷ specialize c pss
... | no _ = specialize c pss
specialize c (((p ∣ q) ∷ ps) ∷ pss) =
  specialize c ((p ∷ ps) ∷ pss) ++ specialize c ((q ∷ ps) ∷ pss)

default : PatMat (α ∷ αs) → PatMat αs
default [] = []
default ((- ∷ ps) ∷ pss) = ps ∷ default pss
default ((con c x ∷ ps) ∷ pss) = default pss
default (((p ∣ q) ∷ ps) ∷ pss) =
  default ((p ∷ ps) ∷ pss) ++ default ((q ∷ ps) ∷ pss)

data _<_ : PatMat αs → PatMat βs → Set where
  []< : ∀ {pss} → _<_ {αs} {βs} [] pss

data Acc (pss : PatMat αs) : Set where
  acc : (∀ {βs} {qss : PatMat βs} → qss < pss → Acc qss) → Acc pss

<-specialize : (c : ctor α) (pss : PatMat (α ∷ αs))
  → specialize c pss < pss
<-specialize c pss = {!   !}

<-default : (pss : PatMat (α ∷ αs)) → default pss < pss
<-default pss = {!   !}

<-wf : (pss : PatMat αs) → Acc pss
<-wf pss = {!   !}

useful?-aux : (ps : Pats αs) (pss : PatMat αs) → Acc pss → Dec (ps Useful pss)
useful?-aux [] [] sh = yes ([] , λ ())
useful?-aux [] ([] ∷ _) sh = no λ { ([] , ¬pss≼[]) → ¬pss≼[] (success []) }
useful?-aux (- ∷ ps) pss (acc h) = {!   !}
useful?-aux (con c ps ∷ qs) pss (acc h) =
  mapDec
    {!   !}
    {!   !}
    (useful?-aux (ps ++ₚ qs) (specialize c pss) (h (<-specialize c pss)))
useful?-aux ((p ∣ q) ∷ ps) pss sh =
  mapDec
    (λ { (inj₁ (p≼v ∷ ps≼vs , ¬pss≼v∷vs)) → ∣₁ p≼v ∷ ps≼vs , ¬pss≼v∷vs
       ; (inj₂ (q≼v ∷ ps≼vs , ¬pss≼v∷vs)) → ∣₂ q≼v ∷ ps≼vs , ¬pss≼v∷vs })
    (λ { (∣₁ p≼v ∷ ps≼vs , ¬pss≼v∷vs) → inj₁ (p≼v ∷ ps≼vs , ¬pss≼v∷vs)
       ; (∣₂ q≼v ∷ ps≼vs , ¬pss≼v∷vs) → inj₂ (q≼v ∷ ps≼vs , ¬pss≼v∷vs) })
    (useful?-aux (p ∷ ps) pss sh ⊎-dec useful?-aux (q ∷ ps) pss sh)

_useful?_ : (ps : Pats αs) (pss : PatMat αs) → Dec (ps Useful pss)
ps useful? pss = useful?-aux ps pss (<-wf pss)

--------------------------------------------------------------------------------

Exhaustive : List (Pat α) → Set
Exhaustive ps = ¬ [ - ] Useful map [_] ps

exhaustive? : (ps : List (Pat α)) → Dec (Exhaustive ps)
exhaustive? ps = ¬? ([ - ] useful? map [_] ps)

--------------------------------------------------------------------------------

`⊤ : Ty
∣ `⊤ ∣ᶜ = 1
args `⊤ zero = []

`⊥ : Ty
∣ `⊥ ∣ᶜ = 0
args `⊥ ()

`Bool : Ty
∣ `Bool ∣ᶜ = 2
args `Bool zero = []
args `Bool (suc zero) = []

`ℕ : Ty
∣ `ℕ ∣ᶜ = 2
args `ℕ zero = []
args `ℕ (suc zero) = `ℕ ∷ []

`Pair : Ty → Ty → Ty
∣ `Pair α β ∣ᶜ = 1
args (`Pair α β) zero = α ∷ β ∷ []

`List : Ty → Ty
∣ `List α ∣ᶜ = 2
args (`List α) zero = []
args (`List α) (suc zero) = α ∷ `List α ∷ []

`tt : Val `⊤
`tt = con0 zero

`false `true : Val `Bool
`false = con0 zero
`true = con0 (suc zero)

`zero : Val `ℕ
`zero = con0 zero

`suc : Val `ℕ → Val `ℕ
`suc n = con (suc zero) [ n ]

infixr 4 _`,_
_`,_ : Val α → Val β → Val (`Pair α β)
x `, y = con zero (x ∷ y ∷ [])

`nil : Val (`List α)
`nil = con0 zero

infixr 5 _`∷_
_`∷_ : Val α → Val (`List α) → Val (`List α)
x `∷ xs = con (suc zero) (x ∷ xs ∷ [])

¬Val`⊥ : ¬ Val `⊥
¬Val`⊥ (con () _)

`zeroₚ : Pat `ℕ
`zeroₚ = con0 zero

`sucₚ : Pat `ℕ → Pat `ℕ
`sucₚ n = con (suc zero) [ n ]

`nilₚ : Pat (`List α)
`nilₚ = con0 zero

infixr 5 _`∷ₚ_
_`∷ₚ_ : Pat α → Pat (`List α) → Pat (`List α)
x `∷ₚ xs = con (suc zero) (x ∷ xs ∷ [])

_ : Pat (`List `ℕ)
_ = `zeroₚ `∷ₚ (`sucₚ `zeroₚ) `∷ₚ (`sucₚ (`sucₚ -)) `∷ₚ -

_ : match (`suc (`suc (`suc `zero))) [ `sucₚ (`sucₚ -) ] ≡
    yes (here (con (suc zero) [ con (suc zero) [ - ] ]))
_ = refl
