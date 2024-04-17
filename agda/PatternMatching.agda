{-# OPTIONS --guardedness #-}

open import Data.Bool using ( T; _∧_; _∨_; not )
open import Data.Empty using ( ⊥-elim )
open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.Fin.Subset using ( Subset; _⊆_; ⊤; ⊥; ⁅_⁆; _∪_; ⋃ )
open import Data.Fin.Subset.Properties using ( _⊆?_ )
open import Data.List as List using ( List; _∷_; []; _++_ )
open import Data.List.Relation.Unary.Any using ( Any; any?; here; there )
open import Data.List.Relation.Unary.All using ( All; all?; _∷_; [] )
open import Data.List.Relation.Unary.All.Properties using ( ++⁺ )
open import Data.Nat using ( ℕ; zero; suc; _≡ᵇ_; NonZero; _⊔_; _≤_ )
open import Data.Product using ( _,_; uncurry )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Vec as Vec using ( Vec; _∷_; []; allFin )
open import Data.Vec.Relation.Unary.All using ( _∷_; [] ) renaming ( all? to all′? )
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
  field args : ctor → List Ty
  ctors = allFin ∣_∣ᶜ

open Ty

private
  variable
    α β : Ty
    αs βs : List Ty

--------------------------------------------------------------------------------

mutual
  data Val (α : Ty) : Set where
    con : (c : ctor α) → Vals (args α c) → Val α

  Vals : List Ty → Set
  Vals = All Val

infixr 5 _∷_

pattern [_] v = v ∷ []
pattern con0 v = con v []

record Nonempty (α : Ty) : Set where
  field
    someVal : Val α

open Nonempty {{...}}

--------------------------------------------------------------------------------

infixr 5 _∣_

mutual
  data Pat (α : Ty) : Set where
    -- Wildcard
    — : Pat α
    -- Constructor pattern
    con : (c : ctor α) → Pats (args α c) → Pat α
    -- Or pattern
    _∣_ : Pat α → Pat α → Pat α

  Pats : List Ty → Set
  Pats = All Pat

pattern [_] v = v ∷ []
pattern con0 v = con v []

height : Pat α → ℕ
height′ : Pats αs → ℕ
height — = 0
height (con c ps) = suc (height′ ps)
height (p ∣ q) = suc (height p ⊔ height q)
height′ [] = 0
height′ (p ∷ ps) = height p ⊔ height′ ps

_≤ₚ_ : Pat α → Pat β → Set
p ≤ₚ q = height p ≤ height q

data Lex : Pats αs → Pats βs → Set where
  halt : ∀ {q : Pat β} {qs : Pats βs} → Lex [] (q ∷ qs)
  this : ∀ {p : Pat α} {ps : Pats αs} {q : Pat β} {qs : Pats βs}
    → p ≤ₚ q
    → Lex ps qs
    → Lex (p ∷ ps) (q ∷ qs)
  next : ∀ {p : Pat α} {ps : Pats αs} {q : Pat β} {qs : Pats βs}
    → height p ≡ height q
    → Lex ps qs
    → Lex (p ∷ ps) (q ∷ qs)

data LexAcc (ps : Pats αs) : Set where
  node : (∀ {βs} {qs : Pats βs} → Lex qs ps → LexAcc qs) → LexAcc ps

Lex-wf : ∀ (ps : Pats αs) → LexAcc ps
Lex-wf [] = node λ ()
Lex-wf (— ∷ ps) = node λ where
  halt → Lex-wf []
  (this q<p qs<ps) → {!   !}
  (next q≡p qs<ps) → {!   !}
Lex-wf (con c ps ∷ qs) = {!   !}
Lex-wf ((p ∣ q) ∷ ps) = {!   !}

—* : Pats αs
—* {[]} = []
—* {α ∷ αs} = — ∷ —* {αs}

PatMat : List Ty → Set
PatMat α = List (Pats α)

first-col : PatMat (α ∷ αs) → List (Pat α)
first-col [] = []
first-col ((p ∷ _) ∷ pss) = p ∷ first-col pss

pat-ctors : Pat α → Subset ∣ α ∣ᶜ
pat-ctors — = ⊥
pat-ctors (con c _) = ⁅ c ⁆
pat-ctors (p ∣ q) = pat-ctors p ∪ pat-ctors q

--------------------------------------------------------------------------------

infix 4 _≼_ _≼*_ _≼**_ _≼?_ _≼*?_ _≼**?_

mutual
  data _≼_ {α} : Pat α → Val α → Set where
    — : ∀ {v} → — ≼ v
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

_≼**_ : PatMat αs → Vals αs → Set
ps ≼** vs = ≼**-aux vs ps

_++≼*_ : ∀ {αs βs} {ps : Pats αs} {qs : Pats βs} {vs : Vals αs} {ws : Vals βs}
  → ps ≼* vs
  → qs ≼* ws
  → (++⁺ ps qs) ≼* (++⁺ vs ws)
[] ++≼* qs≼ws = qs≼ws
(p≼v ∷ ps≼vs) ++≼* qs≼ws = p≼v ∷ (ps≼vs ++≼* qs≼ws)

mutual
  _≼?_ : (p : Pat α) (v : Val α) → Dec (p ≼ v)
  — ≼? v = yes —
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

match? : (v : Val α) (ps : List (Pat α)) → Dec (Any (_≼ v) ps)
match? v = any? (_≼? v)

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
specialize c ((— ∷ ps) ∷ pss) = (++⁺ —* ps) ∷ specialize c pss
specialize c ((con c' ps ∷ qs) ∷ pss) with c ≟ c'
... | yes refl = (++⁺ ps qs) ∷ specialize c pss
... | no _ = specialize c pss
specialize c (((p ∣ q) ∷ ps) ∷ pss) =
  specialize c ((p ∷ ps) ∷ pss) ++ specialize c ((q ∷ ps) ∷ pss)

default : PatMat (α ∷ αs) → PatMat αs
default [] = []
default ((— ∷ ps) ∷ pss) = ps ∷ default pss
default ((con c ps ∷ qs) ∷ pss) = default pss
default (((p ∣ q) ∷ ps) ∷ pss) =
  default ((p ∷ ps) ∷ pss) ++ default ((q ∷ ps) ∷ pss)

lemma11 :
  ∀ {α αs} {c : ctor α} {pss : PatMat (α ∷ αs)} {vs : Vals (args α c)} {ws : Vals αs}
  → ¬ pss ≼** (con c vs ∷ ws)
  → ¬ specialize c pss ≼** ++⁺ vs ws
lemma11 {pss = (— ∷ ps) ∷ pss} h1 h2 = {!   !}
lemma11 {pss = (con c ps ∷ qs) ∷ pss} h1 h2 = {!   !}
lemma11 {pss = ((p ∣ q) ∷ ps) ∷ pss} h1 h2 = {!   !}

lemma11′ :
  ∀ {α αs} {c : ctor α} {pss : PatMat (α ∷ αs)} {vs : Vals (args α c)} {ws : Vals αs}
  → ¬ specialize c pss ≼** ++⁺ vs ws
  → ¬ pss ≼** (con c vs ∷ ws)
lemma11′ = {!   !}

lemma12 : ∀ {α αs} {pss : PatMat (α ∷ αs)} {v : Val α} {vs : Vals αs}
  → ¬ pss ≼** (v ∷ vs)
  → ¬ default pss ≼** vs
lemma12 {pss = (— ∷ ps) ∷ pss} h1 h2 = {!   !}
lemma12 {pss = (con c ps ∷ qs) ∷ pss} h1 h2 = {!   !}
lemma12 {pss = ((p ∣ q) ∷ ps) ∷ pss} h1 h2 = {!   !}

complete? : (pss : PatMat (α ∷ αs))
  → Dec (⊤ ⊆ ⋃ (List.map pat-ctors (first-col pss)))
complete? {α} pss = ⊤ ⊆? ⋃ (List.map pat-ctors (first-col pss))

data Acc : Pats αs → Set where
  stop : Acc []
  step-— : ∀ {α} {ps : Pats αs}
    → ({c : ctor α} → Acc (++⁺ (—* {args α c}) ps))
    → Acc ps
    → Acc {α ∷ αs} (— ∷ ps)
  step-con : {c : ctor α} {ps : Pats (args α c)} {qs : Pats αs}
    → Acc (++⁺ ps qs)
    → Acc {α ∷ αs} (con c ps ∷ qs)
  step-∣ : {p q : Pat α} {ps : Pats αs}
    → Acc (p ∷ ps)
    → Acc (q ∷ ps)
    → Acc ((p ∣ q) ∷ ps)

useful-⊎-∣ : ∀ {p q : Pat α} {ps : Pats αs} {pss}
  → (p ∷ ps) Useful pss ⊎ (q ∷ ps) Useful pss
  → ((p ∣ q) ∷ ps) Useful pss
useful-⊎-∣ (inj₁ (p≼v ∷ ps≼vs , ¬pss≼v∷vs)) = ∣₁ p≼v ∷ ps≼vs , ¬pss≼v∷vs
useful-⊎-∣ (inj₂ (q≼v ∷ ps≼vs , ¬pss≼v∷vs)) = ∣₂ q≼v ∷ ps≼vs , ¬pss≼v∷vs

useful-∣-⊎ : ∀ {p q : Pat α} {ps : Pats αs} {pss}
  → ((p ∣ q) ∷ ps) Useful pss
  → (p ∷ ps) Useful pss ⊎ (q ∷ ps) Useful pss
useful-∣-⊎ (∣₁ p≼v ∷ ps≼vs , ¬pss≼v∷vs) = inj₁ (p≼v ∷ ps≼vs , ¬pss≼v∷vs)
useful-∣-⊎ (∣₂ q≼v ∷ ps≼vs , ¬pss≼v∷vs) = inj₂ (q≼v ∷ ps≼vs , ¬pss≼v∷vs)

useful-specialize-con :
  ∀ {c : ctor α} {ps : Pats (args α c)} {qs : Pats αs} {pss : PatMat (α ∷ αs)}
  → (++⁺ ps qs) Useful specialize c pss
  → (con c ps ∷ qs) Useful pss
useful-specialize-con (ev₁ , ev₂) = {!   !} , lemma11′ ev₂

useful-con-specialize :
  ∀ {c : ctor α} {ps : Pats (args α c)} {qs : Pats αs} {pss : PatMat (α ∷ αs)}
  → (con c ps ∷ qs) Useful pss
  → (++⁺ ps qs) Useful specialize c pss
useful-con-specialize (con _ ps≼vs ∷ qs≼ws , ¬pss≼cvs∷ws) =
  ps≼vs ++≼* qs≼ws , lemma11 ¬pss≼cvs∷ws

useful-—-default : ∀ {α} {ps : Pats αs} {pss : PatMat (α ∷ αs)}
  → (— ∷ ps) Useful pss
  → ps Useful default pss
useful-—-default (- ∷ ps≼vs , ¬pss≼v∷vs) = ps≼vs , lemma12 ¬pss≼v∷vs

useful-default-— : ∀ {α αs} {{_ : Nonempty α}} {ps : Pats αs} {pss : PatMat (α ∷ αs)}
  → ps Useful default pss
  → (— ∷ ps) Useful pss
useful-default-— {α} (ps≼vs , ¬pss≼vs) = — {v = someVal} ∷ ps≼vs , {!   !}

useful?-aux : (ps : Pats αs) (pss : PatMat αs) → Acc ps → Dec (ps Useful pss)
useful?-aux [] [] acc = yes ([] , λ ())
useful?-aux [] ([] ∷ pss) acc = no λ { ([] , ¬pss≼[]) → ¬pss≼[] (success []) }
useful?-aux (_∷_ {α} — ps) pss (step-— acc acc') with complete? pss
... | yes _ =
      mapDec
        {!   !}
        {!   !}
        (all′? (λ c → useful?-aux (++⁺ —* ps) (specialize c pss) acc) (ctors α))
... | no _ =
      mapDec
        -- useful-default-—
        {!   !}
        useful-—-default
        (useful?-aux ps (default pss) acc')
useful?-aux (con c ps ∷ qs) pss (step-con acc) =
  mapDec
    useful-specialize-con
    useful-con-specialize
    (useful?-aux (++⁺ ps qs) (specialize c pss) acc)
useful?-aux ((p ∣ q) ∷ ps) pss (step-∣ acc acc') =
  mapDec
    useful-⊎-∣
    useful-∣-⊎
    (useful?-aux (p ∷ ps) pss acc ⊎-dec useful?-aux (q ∷ ps) pss acc')


∀Acc : (ps : Pats αs) → Acc ps
∀Acc [] = stop
∀Acc (— ∷ ps) = step-— {!   !} (∀Acc ps)
∀Acc (con c ps ∷ qs) = step-con {!   !}
∀Acc ((p ∣ q) ∷ ps) = step-∣ (∀Acc (p ∷ ps)) (∀Acc (q ∷ ps))

_useful?_ : (ps : Pats αs) (pss : PatMat αs) → Dec (ps Useful pss)
ps useful? pss = useful?-aux ps pss (∀Acc ps)

--------------------------------------------------------------------------------

Exhaustive : List (Pat α) → Set
Exhaustive ps = ¬ ([ — ] Useful List.map [_] ps)

exhaustive? : (ps : List (Pat α)) → Dec (Exhaustive ps)
exhaustive? ps = ¬? ([ — ] useful? List.map [_] ps)

--------------------------------------------------------------------------------

`⊤ : Ty
∣ `⊤ ∣ᶜ = 1
args `⊤ zero = []

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

instance
  nonempty⊤ : Nonempty `⊤
  someVal {{nonempty⊤}} = `tt

  nonemptyBool : Nonempty `Bool
  someVal {{nonemptyBool}} = `false

  nonemptyℕ : Nonempty `ℕ
  someVal {{nonemptyℕ}} = `zero

  nonemptyPair : ∀ {α β} {{_ : Nonempty α}} {{_ : Nonempty β}} → Nonempty (`Pair α β)
  someVal {{nonemptyPair}} = someVal `, someVal

  nonemptyList : ∀ {α} → Nonempty (`List α)
  someVal {{nonemptyList}} = `nil

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
_ = `zeroₚ `∷ₚ (`sucₚ `zeroₚ) `∷ₚ (`sucₚ (`sucₚ —)) `∷ₚ —

_ : match? (`suc (`suc (`suc `zero))) [ `sucₚ (`sucₚ —) ] ≡
    yes (here (con (suc zero) [ con (suc zero) [ — ] ]))
_ = refl
