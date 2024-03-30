module STLC where

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Data.Product.Base using ( Σ-syntax; _×_; proj₁; proj₂ ) renaming ( _,_ to ⟨_,_⟩ )
open import Data.Unit.Base using ( ⊤; tt )
open import Function.Base using ( flip; _$_ )
open import Relation.Binary.Definitions using ( _Respects_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using ( Star; ε; _◅_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning )
  renaming ( subst to transport )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness )

private
  variable
    A B C D : Set

--------------------------------------------------------------------------------
-- Misc.

cong₃ : ∀ (f : A → B → C → D) {x y} {u v} {w z}
  → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl

--------------------------------------------------------------------------------
-- Syntax

infixr 7 _⇒_
infix  4 _∋_
infixl 5 _,_
infix  5 ƛ_
infixl 7 _·_
infix  9 #_
infix  2 _⟶_ _⟶*_ _⟵_ _*⟵_

data Type : Set where
  `ℕ : Type
  _⇒_ : (α β : Type) → Type

data Ctx : Set where
  ∅ : Ctx
  _,_ : (Γ : Ctx) (α : Type) → Ctx

private
  variable
    Γ Δ Σ Ψ : Ctx
    α β γ : Type

data _∋_ : Ctx → Type → Set where
  zero : Γ , α ∋ α
  suc : Γ ∋ α → Γ , β ∋ α

data Term : Ctx → Type → Set where
  var : (i : Γ ∋ α) → Term Γ α
  ƛ_ : (t : Term (Γ , α) β) → Term Γ (α ⇒ β)
  _·_ : (t : Term Γ (α ⇒ β)) → (s : Term Γ α) → Term Γ β
  `zero : Term Γ `ℕ
  `suc : Term Γ `ℕ → Term Γ `ℕ
  case : (t : Term Γ `ℕ) (s : Term Γ α) (u : Term (Γ , `ℕ) α) → Term Γ α

length : Ctx → ℕ
length ∅ = 0
length (Γ , _) = suc (length Γ)

lookup : {n : ℕ} (p : n < length Γ) → Type
lookup {_ , α} {zero} (s≤s z≤n) = α
lookup {Γ , _} {suc n} (s≤s p) = lookup p

count : {n : ℕ} (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = zero
count {Γ , _} {suc n} (s≤s p) = suc (count p)

#_ : ∀ (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)} → Term Γ (lookup (toWitness n∈Γ))
#_ n {n∈Γ} = var (count (toWitness n∈Γ))

--------------------------------------------------------------------------------
-- Semantics

Rename : Ctx → Ctx → Set
Rename Γ Δ = ∀ {α} → Γ ∋ α → Δ ∋ α

Subst : Ctx → Ctx → Set
Subst Γ Δ = ∀ {α} → Γ ∋ α → Term Δ α

ext : Rename Γ Δ → Rename (Γ , α) (Δ , α)
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)

rename : Rename Γ Δ → Term Γ α → Term Δ α
rename ρ (var i) = var (ρ i)
rename ρ (ƛ t) = ƛ (rename (ext ρ) t)
rename ρ (t · s) = rename ρ t · rename ρ s
rename ρ `zero = `zero
rename ρ (`suc t) = `suc (rename ρ t)
rename ρ (case t s u) = case (rename ρ t) (rename ρ s) (rename (ext ρ) u)

exts : Subst Γ Δ → Subst (Γ , α) (Δ , α)
exts σ zero = var zero
exts σ (suc i) = rename suc (σ i)

subst : Subst Γ Δ → Term Γ α → Term Δ α
subst σ (var i) = σ i
subst σ (ƛ t) = ƛ (subst (exts σ) t)
subst σ (t · s) = subst σ t · subst σ s
subst σ `zero = `zero
subst σ (`suc t) = `suc (subst σ t)
subst σ (case t s u) = case (subst σ t) (subst σ s) (subst (exts σ) u)

ids : Subst Γ Γ
ids = var

shift : Subst Γ (Γ , α)
shift i = var (suc i)

infixl 6 _∷_
_∷_ : Subst Γ Δ → Term Δ α → Subst (Γ , α) Δ
(σ ∷ t) zero = t
(σ ∷ t) (suc i) = σ i

infixr 5 _∙_
_∙_ : Subst Δ Σ → Subst Γ Δ → Subst Γ Σ
(σ ∙ σ') i = subst σ (σ' i)

_[_] : ∀ {α β} → Term (Γ , β) α → Term Γ β → Term Γ α
t [ t' ] = subst (ids ∷ t') t

data Value : Term Γ α → Set where
  V-ƛ : {t : Term (Γ , α) β} → Value (ƛ t)
  V-zero : Value (`zero {Γ})
  V-suc : {v : Term Γ `ℕ} → Value v → Value (`suc v)

-- Call by value
data _⟶_ : Term Γ α → Term Γ α → Set where

  ξ-·₁ : {t t' : Term Γ (α ⇒ β)} {s : Term Γ α}
    → t ⟶ t'
    → t · s ⟶ t' · s

  ξ-·₂ : {t : Term Γ (α ⇒ β)} {s s' : Term Γ α}
    → Value t
    → s ⟶ s'
    → t · s ⟶ t · s'

  β-ƛ : {t : Term (Γ , α) β} {v : Term Γ α}
    → Value v
    → (ƛ t) · v ⟶ t [ v ]

  ξ-suc : {t t' : Term Γ `ℕ}
    → t ⟶ t'
    → `suc t ⟶ `suc t'

  ξ-case : {t t' : Term Γ `ℕ} {s : Term Γ α} {u : Term (Γ , `ℕ) α}
    → t ⟶ t'
    → case t s u ⟶ case t' s u

  β-zero : {s : Term Γ α} {u : Term (Γ , `ℕ) α}
    → case `zero s u ⟶ s

  β-suc : {v : Term Γ `ℕ} {s : Term Γ α} {u : Term (Γ , `ℕ) α}
    → Value v
    → case (`suc v) s u ⟶ u [ v ]

_⟵_ _⟶*_ _*⟵_ : Term Γ α → Term Γ α → Set
_⟵_ = flip _⟶_
_⟶*_ = Star _⟶_
_*⟵_ = flip _⟶*_

module ⟶*-Reasoning {Γ α} where
  open StarReasoning (_⟶_ {Γ} {α}) public

--------------------------------------------------------------------------------
-- Values do not reduce

V¬⟶ : {v v' : Term Γ α} → Value v → ¬ (v ⟶ v')
V¬⟶ V-ƛ ()
V¬⟶ V-zero ()
V¬⟶ (V-suc p) (ξ-suc r) = V¬⟶ p r

--------------------------------------------------------------------------------
-- ⟶ is deterministic

⟶-deterministic : {t s u : Term Γ α} → t ⟶ s → t ⟶ u → s ≡ u
⟶-deterministic (β-ƛ _) (β-ƛ _) = refl
⟶-deterministic β-zero β-zero = refl
⟶-deterministic (β-suc _) (β-suc _) = refl
⟶-deterministic (ξ-·₁ t⟶s) (ξ-·₂ V t⟶u) = ⊥-elim (V¬⟶ V t⟶s)
⟶-deterministic (ξ-·₂ V t⟶s) (ξ-·₁ t⟶u) = ⊥-elim (V¬⟶ V t⟶u)
⟶-deterministic (ξ-·₂ _ t⟶s) (β-ƛ V) = ⊥-elim (V¬⟶ V t⟶s)
⟶-deterministic (β-ƛ V) (ξ-·₂ _ t⟶u) = ⊥-elim (V¬⟶ V t⟶u)
⟶-deterministic (ξ-case t⟶s) (β-suc V) = ⊥-elim (V¬⟶ (V-suc V) t⟶s)
⟶-deterministic (β-suc V) (ξ-case t⟶u) = ⊥-elim (V¬⟶ (V-suc V) t⟶u)
⟶-deterministic (ξ-·₁ t⟶s) (ξ-·₁ t⟶u) = cong (_· _) (⟶-deterministic t⟶s t⟶u)
⟶-deterministic (ξ-·₂ _ t⟶s) (ξ-·₂ _ t⟶u) = cong (_ ·_) (⟶-deterministic t⟶s t⟶u)
⟶-deterministic (ξ-suc t⟶s) (ξ-suc t⟶u) = cong `suc (⟶-deterministic t⟶s t⟶u)
⟶-deterministic (ξ-case t⟶s) (ξ-case t⟶u) = cong (λ t → case t _ _) (⟶-deterministic t⟶s t⟶u)

--------------------------------------------------------------------------------
-- Properties of substitution

cong-exts : {σ σ' : Subst Γ Δ}
  → (∀ {α} (i : Γ ∋ α) → σ i ≡ σ' i)
  → (i : Γ , α ∋ β)
  → exts σ i ≡ exts σ' i
cong-exts σ≡σ' zero = refl
cong-exts σ≡σ' (suc i) = cong (rename suc) (σ≡σ' i)

cong-subst : {σ σ' : Subst Γ Δ}
  → (∀ {α} (i : Γ ∋ α) → σ i ≡ σ' i)
  → (t : Term Γ α)
  → subst σ t ≡ subst σ' t
cong-subst σ≡σ' (var i) = σ≡σ' i
cong-subst σ≡σ' (ƛ t) = cong ƛ_ (cong-subst (cong-exts σ≡σ') t)
cong-subst σ≡σ' (t · s) = cong₂ _·_ (cong-subst σ≡σ' t) (cong-subst σ≡σ' s)
cong-subst σ≡σ' `zero = refl
cong-subst σ≡σ' (`suc t) = cong `suc (cong-subst σ≡σ' t)
cong-subst σ≡σ' (case t s u) =
  cong₃ case (cong-subst σ≡σ' t) (cong-subst σ≡σ' s) (cong-subst (cong-exts σ≡σ') u)

exts-ids : (i : Γ , α ∋ β) → exts ids i ≡ ids i
exts-ids zero = refl
exts-ids (suc i) = refl

exts-∙ : (σ : Subst Δ Σ) (σ' : Subst Γ Δ) (i : Γ , α ∋ β)
  → (exts σ ∙ exts σ') i ≡ exts (σ ∙ σ') i
exts-∙ σ σ' zero = refl
exts-∙ σ σ' (suc i) = {!   !}

ren : Rename Γ Δ → Subst Γ Δ
ren ρ i = ids (ρ i)

ren-ext : ∀ (ρ : Rename Γ Δ) (i : Γ , α ∋ β)
  → ren (ext ρ) i ≡ exts (ren ρ) i
ren-ext ρ zero = refl
ren-ext ρ (suc i) = refl

rename-subst-ren : ∀ (ρ : Rename Γ Δ) (t : Term Γ α)
  → rename ρ t ≡ subst (ren ρ) t
rename-subst-ren ρ (var i) = refl
rename-subst-ren ρ (ƛ t) =
  cong ƛ_ (trans (rename-subst-ren (ext ρ) t) (cong-subst (ren-ext ρ) t))
rename-subst-ren ρ (t · s) = cong₂ _·_ (rename-subst-ren ρ t) (rename-subst-ren ρ s)
rename-subst-ren ρ `zero = refl
rename-subst-ren ρ (`suc t) = cong `suc (rename-subst-ren ρ t)
rename-subst-ren ρ (case t s u) =
  cong₃ case (rename-subst-ren ρ t) (rename-subst-ren ρ s) (trans (rename-subst-ren (ext ρ) u) (cong-subst (ren-ext ρ) u))

subst-id : (t : Term Γ α) → subst ids t ≡ t
subst-id (var i) = refl
subst-id (ƛ t) = cong ƛ_ (trans (cong-subst exts-ids t) (subst-id t))
subst-id (t · s) = cong₂ _·_ (subst-id t) (subst-id s)
subst-id `zero = refl
subst-id (`suc t) = cong `suc (subst-id t)
subst-id (case t s u) =
  cong₃ case (subst-id t) (subst-id s) (trans (cong-subst exts-ids u) (subst-id u))

subst-subst : (σ : Subst Δ Σ) (σ' : Subst Γ Δ) (t : Term Γ α)
  → subst σ (subst σ' t) ≡ subst (σ ∙ σ') t
subst-subst σ σ' (var i) = refl
subst-subst σ σ' (ƛ t) =
  cong ƛ_ (trans (subst-subst (exts σ) (exts σ') t) (cong-subst (exts-∙ σ σ') t))
subst-subst σ σ' (t · s) = cong₂ _·_ (subst-subst σ σ' t) (subst-subst σ σ' s)
subst-subst σ σ' `zero = refl
subst-subst σ σ' (`suc t) = cong `suc (subst-subst σ σ' t)
subst-subst σ σ' (case t s u) =
  cong₃ case (subst-subst σ σ' t) (subst-subst σ σ' s) (trans (subst-subst (exts σ) (exts σ') u) (cong-subst (exts-∙ σ σ') u))

subst-assoc : (σ : Subst Σ Ψ) (τ : Subst Δ Σ) (θ : Subst Γ Δ) (i : Γ ∋ α)
  → ((σ ∙ τ) ∙ θ) i ≡ (σ ∙ (τ ∙ θ)) i
subst-assoc σ τ θ i = {!   !}

vacuous-subst : Subst Γ Γ
vacuous-subst {∅} = λ ()
vacuous-subst {Γ , α} = exts (vacuous-subst {Γ})

vacuous-subst≡ids : (i : Γ ∋ α) → vacuous-subst i ≡ ids i
vacuous-subst≡ids zero = refl
vacuous-subst≡ids (suc i) = cong (rename suc) (vacuous-subst≡ids i)

subst-closed : (t : Term ∅ α) → subst (λ ()) t ≡ t
subst-closed t = trans (cong-subst vacuous-subst≡ids t) (subst-id t)

--------------------------------------------------------------------------------
-- Progress

data Progress (t : Term ∅ α) : Set where
  done : Value t → Progress t
  step : {t' : Term ∅ α} → t ⟶ t' → Progress t

progress : (t : Term ∅ α) → Progress t
progress (ƛ t) = done V-ƛ
progress (t · s) with progress t
... | step t⟶t' = step (ξ-·₁ t⟶t')
... | done V-ƛ with progress s
...   | step s⟶s' = step (ξ-·₂ V-ƛ s⟶s')
...   | done v = step (β-ƛ v)
progress `zero = done V-zero
progress (`suc t) with progress t
... | step t⟶t' = step (ξ-suc t⟶t')
... | done v = done (V-suc v)
progress (case t s u) with progress t
... | step t⟶t' = step (ξ-case t⟶t')
... | done V-zero = step β-zero
... | done (V-suc v) = step (β-suc v)

--------------------------------------------------------------------------------
-- Strong normalization

infix 3 _⇓

data _⇓ {α} : Term ∅ α → Set where
  steps : {t v : Term ∅ α} → t ⟶* v → Value v → t ⇓

SN : Term ∅ α → Set
SN {`ℕ} t = t ⇓
SN {α ⇒ β} t = t ⇓ × (∀ {s} → SN {α} s → SN {β} (t · s))

SN-⇓ : {t : Term ∅ α} → SN t → t ⇓
SN-⇓ {`ℕ} t⇓ = t⇓
SN-⇓ {α ⇒ β} ⟨ t⇓ , _ ⟩ = t⇓

⇓-respects-⟶ : {t t' : Term ∅ α} → t ⟶ t' → t ⇓ → t' ⇓
⇓-respects-⟶ t⟶t' (steps ε v) = ⊥-elim (V¬⟶ v t⟶t')
⇓-respects-⟶ t⟶t' (steps (t⟶t'' ◅ t''⟶*v) v) =
  transport _⇓ (⟶-deterministic t⟶t'' t⟶t') (steps t''⟶*v v)

SN-respects-⟶ : {t t' : Term ∅ α} → t ⟶ t' → SN t → SN t'
SN-respects-⟶ {`ℕ} t⟶t' t⇓ = ⇓-respects-⟶ t⟶t' t⇓
SN-respects-⟶ {α ⇒ β} t⟶t' ⟨ t⇓ , SNs→SN[t·s] ⟩ =
  ⟨ ⇓-respects-⟶ t⟶t' t⇓ , (λ SNs → SN-respects-⟶ (ξ-·₁ t⟶t') (SNs→SN[t·s] SNs)) ⟩

SN-respects-⟶* : {t t' : Term ∅ α} → t ⟶* t' → SN t → SN t'
SN-respects-⟶* ε SNt = SNt
SN-respects-⟶* (t⟶s ◅ s⟶*t') SNt =
  SN-respects-⟶* s⟶*t' (SN-respects-⟶ t⟶s SNt)

⇓-respects-⟵ : {t t' : Term ∅ α} → t' ⟵ t → t' ⇓ → t ⇓
⇓-respects-⟵ t⟶t' (steps t'⟶*v Vv) = steps (t⟶t' ◅ t'⟶*v) Vv

SN-respects-⟵ : {t t' : Term ∅ α} → t' ⟵ t → SN t' → SN t
SN-respects-⟵ {`ℕ} t⟶t' t'⇓ = ⇓-respects-⟵ t⟶t' t'⇓
SN-respects-⟵ {α ⇒ β} t⟶t' ⟨ t'⇓ , SNs→SN[t'·s] ⟩ =
  ⟨ ⇓-respects-⟵ t⟶t' t'⇓ , (λ SNs → SN-respects-⟵ (ξ-·₁ t⟶t') (SNs→SN[t'·s] SNs)) ⟩

SN-respects-*⟵ : {t t' : Term ∅ α} → t' *⟵ t → SN t' → SN t
SN-respects-*⟵ ε SNt = SNt
SN-respects-*⟵ (t⟶s ◅ s⟶*t') SNt' =
  SN-respects-⟵ t⟶s (SN-respects-*⟵ s⟶*t' SNt')

subst-uncons : ∀ (σ : ∀ {α} → Γ ∋ α → Term Δ α) {α β} (t : Term Δ β) (s : Term (Γ , β) α)
  → subst (σ ∷ t) s ≡ subst (exts σ) s [ t ]
subst-uncons σ t s = {!   !}

SN-∷ : {σ : ∀ {α} → Γ ∋ α → Term ∅ α}
  → (∀ {α} (i : Γ ∋ α) → SN (σ i))
  → {t : Term ∅ β} → SN t
  → (∀ {α} (i : Γ , β ∋ α) → SN ((σ ∷ t) i))
SN-∷ SNσ SNt zero = SNt
SN-∷ SNσ SNt (suc i) = SNσ i

module _ where
  open ⟶*-Reasoning
  open import Relation.Binary.PropositionalEquality.TrustMe

  Term-SN′ :
      {σ : ∀ {α} → Γ ∋ α → Term ∅ α}
    → (∀ {α} (i : Γ ∋ α) → SN (σ i))
    → (t : Term Γ α)
    → SN (subst σ t)
  Term-SN′ SNσ (var i) = SNσ i
  Term-SN′ {σ = σ} SNσ (ƛ t) = ⟨ steps ε V-ƛ , h ⟩
    where
      h : ∀ {s} → SN s → SN ((ƛ subst (exts σ) t) · s)
      h {s} SNs with steps {v = v} s⟶*v V-v ← SN-⇓ SNs =
        let ih = Term-SN′ (SN-∷ SNσ (SN-respects-⟶* s⟶*v SNs)) t in
        flip SN-respects-*⟵ ih $ begin
          (ƛ subst (exts σ) t) · s  ⟶*⟨ Star.gmap _ (ξ-·₂ V-ƛ) s⟶*v ⟩
          (ƛ subst (exts σ) t) · v  ⟶⟨ β-ƛ V-v ⟩
          subst (exts σ) t [ v ]    ≡⟨ trustMe {- subst-uncons σ v t -} ⟨
          subst (σ ∷ v) t           ∎
  Term-SN′ SNσ (t · s) = proj₂ (Term-SN′ SNσ t) (Term-SN′ SNσ s)
  Term-SN′ SNσ `zero = steps ε V-zero
  Term-SN′ SNσ (`suc t) with steps t'⟶*v v ← Term-SN′ SNσ t =
    steps (Star.gmap `suc ξ-suc t'⟶*v) (V-suc v)
  Term-SN′ {σ = σ} SNσ (case t s u) with Term-SN′ SNσ t
  ... | steps {v = `zero} t⟶*v V-zero =
        flip SN-respects-*⟵ (Term-SN′ SNσ s) $ begin
          case (subst σ t) (subst σ s) (subst (exts σ) u)  ⟶*⟨ Star.gmap _ ξ-case t⟶*v ⟩
          case `zero (subst σ s) (subst (exts σ) u)        ⟶⟨ β-zero ⟩
          subst σ s                                        ∎
  ... | steps {v = `suc v} t⟶*v (V-suc V-v) =
        let ih = Term-SN′ (SN-∷ SNσ (steps ε V-v)) u in
        flip SN-respects-*⟵ ih $ begin
          case (subst σ t) (subst σ s) (subst (exts σ) u)  ⟶*⟨ Star.gmap _ ξ-case t⟶*v ⟩
          case (`suc v) (subst σ s) (subst (exts σ) u)     ⟶⟨ β-suc V-v ⟩
          subst (exts σ) u [ v ]                           ≡⟨ trustMe {- subst-uncons σ v u -} ⟨
          subst (σ ∷ v) u                                  ∎

Term-SN : (t : Term ∅ α) → SN t
Term-SN t = transport SN (subst-closed t) (Term-SN′ (λ ()) t)

Term-⇓ : (t : Term ∅ α) → t ⇓
Term-⇓ t = SN-⇓ (Term-SN t)

eval : (t : Term ∅ α) → Σ[ v ∈ Term ∅ α ] Value v
eval t with steps {v = v} _ V-v ← Term-⇓ t = ⟨ v , V-v ⟩

eval-steps : (t : Term ∅ α) → t ⟶* proj₁ (eval t)
eval-steps t with steps {v = v} t⟶*v _ ← Term-⇓ t = t⟶*v

--------------------------------------------------------------------------------
-- Examples

Ch : Type → Type
Ch α = (α ⇒ α) ⇒ α ⇒ α

`_ : ℕ → Term Γ `ℕ
` zero = `zero
` suc n = `suc (` n)

_ᶜ′ : ℕ → Term (Γ , α ⇒ α , α) α
zero ᶜ′ = # 0
(suc n) ᶜ′ = # 1 · n ᶜ′

_ᶜ : ℕ → Term Γ (Ch α)
n ᶜ = ƛ ƛ n ᶜ′

plusᶜ : Term ∅ (Ch α ⇒ Ch α ⇒ Ch α)
plusᶜ = ƛ ƛ ƛ ƛ # 3 · # 1 · (# 2 · # 1 · # 0)

multᶜ : Term ∅ (Ch α ⇒ Ch α ⇒ Ch α)
multᶜ = ƛ ƛ ƛ ƛ # 3 · (# 2 · # 1) · # 0

_ : eval (multᶜ · (2 ᶜ) · (3 ᶜ) · (ƛ `suc (# 0)) · `zero) ≡ eval (` 6)
_ = refl
