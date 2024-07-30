module GrabDelimit where

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function using ( flip; _$_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using ( Star; ε; _◅_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning )
  renaming ( subst to transport )
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ) renaming ( refl to hrefl )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness )

--------------------------------------------------------------------------------

infixr 7 _⇒_!_
infix  4 _∋_
infixl 5 _,_
infix  5 ƛ_
infixl 7 _·_
infix  9 #_
infix  2 _⟶_ _⟶*_ _⟵_ _*⟵_

data Ty : Set
data Eff : Set

data Ty where
  `ℕ : Ty
  _⇒_!_ : Ty → Ty → Eff → Ty

data Eff where
  ι : Eff
  _,_ : Eff → Ty → Eff

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Ty → Ctx

private
  variable
    Γ Δ Σ Ψ : Ctx
    α β γ αₕ βₕ : Ty
    E E' E'' Eₕ : Eff

data _∋_ : Ctx → Ty → Set where
  zero : Γ , α ∋ α
  suc : Γ ∋ α → Γ , β ∋ α

data Term : Ctx → Eff → Ty → Set where
  var : Γ ∋ α → Term Γ E α
  ƛ_ : Term (Γ , α) E β → Term Γ E' (α ⇒ β ! E)
  _·_ : Term Γ E (α ⇒ β ! E) → Term Γ E α → Term Γ E β
  delimit : Term Γ (E , α) α → Term Γ E α
  grab : Term (Γ , α ⇒ β ! E) E β → Term Γ (E , β) α
  zero : Term Γ E `ℕ
  suc : Term Γ E `ℕ → Term Γ E `ℕ
  case : Term Γ E α → Term (Γ , `ℕ) E α → Term Γ E `ℕ → Term Γ E α

PureTerm : Ctx → Ty → Set
PureTerm Γ α = ∀ {E} → Term Γ E α

length : Ctx → ℕ
length ∅ = 0
length (Γ , _) = suc (length Γ)

lookup : ∀ {n} → n < length Γ → Ty
lookup {_ , α} {zero} (s≤s z≤n) = α
lookup {Γ , _} {suc n} (s≤s p) = lookup p

count : ∀ {n} (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = zero
count {Γ , _} {suc n} (s≤s p) = suc (count p)

#_ : ∀ n {n∈Γ : True (suc n ≤? length Γ)} → Term Γ E (lookup (toWitness n∈Γ))
#_ n {n∈Γ} = var (count (toWitness n∈Γ))

_ : Term (∅ , α ⇒ α ! (ι , α) , α) ι α
_ = delimit (# 1 · grab (# 0 · # 1))

_ : Term (∅ , α) (ι , α , α) α
_ = grab (grab (# 0 · # 2))

-- delimit (suc (grab k. k (k 0)))
ex : Term ∅ ι `ℕ
ex = delimit (suc (grab (# 0 · (# 0 · zero))))

--------------------------------------------------------------------------------

Rename : Ctx → Ctx → Set
Rename Γ Δ = ∀ {α} → Γ ∋ α → Δ ∋ α

ext : Rename Γ Δ → Rename (Γ , α) (Δ , α)
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)

rename : Rename Γ Δ → Term Γ E α → Term Δ E α
rename ρ (var i) = var (ρ i)
rename ρ (ƛ t) = ƛ rename (ext ρ) t
rename ρ (t · u) = rename ρ t · rename ρ u
rename ρ (delimit t) = delimit (rename ρ t)
rename ρ (grab t) = grab (rename (ext ρ) t)
rename ρ zero = zero
rename ρ (suc t) = suc (rename ρ t)
rename ρ (case s t u) = case (rename ρ s) (rename (ext ρ) t) (rename ρ u)

↑ : Term Γ E α → Term (Γ , β) E α
↑ = rename suc

--------------------------------------------------------------------------------

Subst : Ctx → Ctx → Set
Subst Γ Δ = ∀ {α} → Γ ∋ α → (∀ {E} → Term Δ E α)

exts : Subst Γ Δ → Subst (Γ , α) (Δ , α)
exts σ zero = var zero
exts σ (suc i) = ↑ (σ i)

subst : Subst Γ Δ → Term Γ E α → Term Δ E α
subst σ (var i) = σ i
subst σ (ƛ t) = ƛ subst (exts σ) t
subst σ (t · u) = subst σ t · subst σ u
subst σ (delimit t) = delimit (subst σ t)
subst σ (grab t) = grab (subst (exts σ) t)
subst σ zero = zero
subst σ (suc t) = suc (subst σ t)
subst σ (case s t u) = case (subst σ s) (subst (exts σ) t) (subst σ u)

_[_] : Term (Γ , α) E β → (∀ {E'} → Term Γ E' α) → Term Γ E β
t [ u ] = subst (λ { zero → u; (suc i) → var i }) t

--------------------------------------------------------------------------------

data Value : Term Γ E α → Set where
  ƛ_ : (t : Term (Γ , α) E β) → Value {E = E'} (ƛ t)
  zero : Value {Γ = Γ} {E = E} zero
  suc : {t : Term Γ E `ℕ} → Value t → Value (suc t)

renameV : (ρ : Rename Γ Δ) {t : Term Γ E α} → Value t → Value (rename ρ t)
renameV ρ (ƛ t) = ƛ rename (ext ρ) t
renameV ρ zero = zero
renameV ρ (suc v) = suc (renameV ρ v)

↑V : {t : Term Γ E α} → Value t → Value (↑ {β = β} t)
↑V = renameV suc

coe : {t : Term Γ E α} → Value t → Term Γ E' α
coe (ƛ t) = ƛ t
coe zero = zero
coe (suc v) = suc (coe v)

data InCtx (h : Term Γ Eₕ αₕ) : Term Γ E α → Set where
  ⟨⟩ : InCtx h h
  _·₁_ : {t : Term Γ E (α ⇒ β ! E)}
    → InCtx h t
    → (u : Term Γ E α)
    → InCtx h (t · u)
  _·₂_ : {v : Term Γ E (α ⇒ β ! E)} {u : Term Γ E α}
    → Value v
    → InCtx h u
    → InCtx h (v · u)
  suc : {t : Term Γ E `ℕ}
    → InCtx h t
    → InCtx h (suc t)
  case : (s : Term Γ E α) (t : Term (Γ , `ℕ) E α) {u : Term Γ E `ℕ}
    → InCtx h u
    → InCtx h (case s t u)

_⟨_⟩ : {h : Term Γ Eₕ αₕ} {t : Term Γ E α}
  → InCtx h t
  → Term Γ Eₕ αₕ
  → Term Γ E α
⟨⟩ ⟨ u ⟩ = u
(c ·₁ t) ⟨ u ⟩ = c ⟨ u ⟩ · t
(_·₂_ {v = v} _ c) ⟨ u ⟩ = v · (c ⟨ u ⟩)
suc c ⟨ u ⟩ = suc (c ⟨ u ⟩)
case s t c ⟨ u ⟩ = case s t (c ⟨ u ⟩)

rename⟨⟩ : (ρ : Rename Γ Δ) {h : Term Γ E α} {t : Term Γ E' β}
  → (c : InCtx h t)
  → InCtx (rename ρ h) (rename ρ t)
rename⟨⟩ ρ ⟨⟩ = ⟨⟩
rename⟨⟩ ρ (c ·₁ u) = rename⟨⟩ ρ c ·₁ rename ρ u
rename⟨⟩ ρ (v ·₂ c) = renameV ρ v ·₂ rename⟨⟩ ρ c
rename⟨⟩ ρ (suc c) = suc (rename⟨⟩ ρ c)
rename⟨⟩ ρ (case s t c) = case (rename ρ s) (rename (ext ρ) t) (rename⟨⟩ ρ c)

↑⟨⟩ : {h : Term Γ Eₕ αₕ} {t : Term Γ E α}
  → InCtx h t
  → InCtx (↑ {β = β} h) (↑ {β = β} t)
↑⟨⟩ = rename⟨⟩ suc

data _⟶_ : Term Γ E α → Term Γ E α → Set where
  β-ƛ : {t : Term (Γ , α) E β} {u : Term Γ E α}
    → (v : Value u)
    → (ƛ t) · u ⟶ t [ coe v ]

  β-delimit₁ : {t : Term Γ (E , α) α}
    → (v : Value t)
    → delimit t ⟶ coe v

  β-delimit₂ : {t : Term Γ (E , β) β} {u : Term (Γ , α ⇒ β ! E) E β}
    → (c : InCtx (grab u) t)
    → delimit t ⟶ u [ ƛ delimit ((↑⟨⟩ c) ⟨ # 0 ⟩) ]

  β-zero : {t : Term Γ E α} {u : Term (Γ , `ℕ) E α}
    → case t u zero ⟶ t

  β-suc : {t : Term Γ E α} {u : Term (Γ , `ℕ) E α} {n : Term Γ E `ℕ}
    → (v : Value n)
    → case t u (suc n) ⟶ u [ coe v ]

  ξ-·₁ : {t t' : Term Γ E (α ⇒ β ! E)} {u : Term Γ E α}
    → t ⟶ t'
    → t · u ⟶ t' · u

  ξ-·₂ : {v : Term Γ E (α ⇒ β ! E)} {t t' : Term Γ E α}
    → Value v
    → t ⟶ t'
    → v · t ⟶ v · t'

  ξ-delimit : {t t' : Term Γ (E , α) α}
    → t ⟶ t'
    → delimit t ⟶ delimit t'

  ξ-suc : {t t' : Term Γ E `ℕ}
    → t ⟶ t'
    → suc t ⟶ suc t'

  ξ-case : {s : Term Γ E α} {t : Term (Γ , `ℕ) E α} {u u' : Term Γ E `ℕ}
    → u ⟶ u'
    → case s t u ⟶ case s t u'

_⟵_ _⟶*_ _*⟵_ : Term Γ E α → Term Γ E α → Set
_⟵_ = flip _⟶_
_⟶*_ = Star _⟶_
_*⟵_ = flip _⟶*_

module ⟶*-Reasoning {Γ E α} where
  open StarReasoning (_⟶_ {Γ} {E} {α}) public

_ : ex ⟶* suc (suc zero)
_ =
  begin
    ex
  ≡⟨⟩
    delimit (suc (grab (# 0 · (# 0 · zero))))
  ⟶⟨ β-delimit₂ (suc ⟨⟩) ⟩
    (# 0 · (# 0 · zero)) [ ƛ delimit (suc (# 0)) ]
  ≡⟨⟩
    (ƛ delimit (suc (# 0))) · ((ƛ delimit (suc (# 0))) · zero)
  ⟶⟨ ξ-·₂ (ƛ delimit (suc (# 0))) (β-ƛ zero) ⟩
    (ƛ delimit (suc (# 0))) · delimit (suc zero)
  ⟶⟨ ξ-·₂ (ƛ delimit (suc (# 0))) (β-delimit₁ (suc zero)) ⟩
    (ƛ delimit (suc (# 0))) · suc zero
  ⟶⟨ β-ƛ (suc zero) ⟩
    delimit (suc (suc zero))
  ⟶⟨ β-delimit₁ (suc (suc (zero))) ⟩
    suc (suc zero)
  ∎
  where open ⟶*-Reasoning

--------------------------------------------------------------------------------
-- Soundness
-- Preservation holds by construction.

data Progress : Term ∅ E α → Set where
  done : {t : Term ∅ E α} → Value t → Progress t
  step : {t t' : Term ∅ E α} → t ⟶ t' → Progress t
  bare-grab : {t : Term ∅ (E , α) β} {u : Term (∅ , γ ⇒ α ! E) E α}
    → InCtx (grab u) t
    → Progress t

progress : (t : Term ∅ E α) → Progress t
progress (ƛ t) = done (ƛ t)
progress (t · u) with progress t
... | step t⟶t' = step (ξ-·₁ t⟶t')
... | bare-grab c = bare-grab (c ·₁ u)
... | done (ƛ t') with progress u
...   | step u⟶u' = step (ξ-·₂ (ƛ t') u⟶u')
...   | done vu = step (β-ƛ vu)
...   | bare-grab c = bare-grab ((ƛ t') ·₂ c)
progress (delimit t) with progress t
... | done vt = step (β-delimit₁ vt)
... | step t⟶t' = step (ξ-delimit t⟶t')
... | bare-grab c = step (β-delimit₂ c)
progress (grab t) = bare-grab ⟨⟩
progress zero = done zero
progress (suc t) with progress t
... | done vt = done (suc vt)
... | step t⟶t' = step (ξ-suc t⟶t')
... | bare-grab c = bare-grab (suc c)
progress (case s t u) with progress u
... | done zero = step β-zero
... | done (suc vu) = step (β-suc vu)
... | step u⟶u' = step (ξ-case u⟶u')
... | bare-grab c = bare-grab (case s t c)

--------------------------------------------------------------------------------

V¬⟶ : {v v' : Term Γ E α} → Value v → ¬ (v ⟶ v')
V¬⟶ (suc v) (ξ-suc v⟶v') = V¬⟶ v v⟶v'

V-unique : {t : Term Γ E α} (v v' : Value t) → v ≡ v'
V-unique (ƛ t) (ƛ .t) = refl
V-unique zero zero = refl
V-unique (suc v) (suc v') = cong suc (V-unique v v')

V¬⟨grab⟩ : {t : Term Γ E α} {u : Term (Γ , αₕ ⇒ βₕ ! Eₕ) Eₕ βₕ}
  → Value t
  → ¬ InCtx (grab u) t
V¬⟨grab⟩ (suc v) (suc c) = V¬⟨grab⟩ v c

⟨grab⟩¬⟶ : {u : Term (Γ , αₕ ⇒ βₕ ! Eₕ) Eₕ βₕ} {t t' : Term Γ E α}
  → InCtx (grab u) t
  → ¬ (t ⟶ t')
⟨grab⟩¬⟶ (c ·₁ u) (ξ-·₁ t⟶t') = ⟨grab⟩¬⟶ c t⟶t'
⟨grab⟩¬⟶ (c ·₁ u) (ξ-·₂ v t⟶t') = ⊥-elim (V¬⟨grab⟩ v c)
⟨grab⟩¬⟶ (v ·₂ c) (β-ƛ u) = ⊥-elim (V¬⟨grab⟩ u c)
⟨grab⟩¬⟶ (v ·₂ c) (ξ-·₁ t⟶t') = ⊥-elim (V¬⟶ v t⟶t')
⟨grab⟩¬⟶ (v ·₂ c) (ξ-·₂ u t⟶t') = ⟨grab⟩¬⟶ c t⟶t'
⟨grab⟩¬⟶ (suc c) (ξ-suc t⟶t') = ⟨grab⟩¬⟶ c t⟶t'
⟨grab⟩¬⟶ (case s t c) (β-suc v) = ⊥-elim (V¬⟨grab⟩ (suc v) c)
⟨grab⟩¬⟶ (case s t c) (ξ-case t⟶t') = ⟨grab⟩¬⟶ c t⟶t'

-- ⟶-deterministic : {t s u : Term Γ E α} → t ⟶ s → t ⟶ u → s ≡ u
-- ⟶-deterministic (β-ƛ {t = t} v) (β-ƛ v') = cong (λ u → t [ coe u ]) (V-unique v v')
-- ⟶-deterministic (β-delimit₁ v) (β-delimit₁ v') = cong coe (V-unique v v')
-- ⟶-deterministic (β-delimit₂ c) (β-delimit₂ c') = {!   !}
-- ⟶-deterministic β-zero β-zero = refl
-- ⟶-deterministic (β-suc {u = t} v) (β-suc v') = cong (λ u → t [ coe u ]) (V-unique v v')
-- ⟶-deterministic (ξ-suc t⟶s) (ξ-suc t⟶u) = cong suc (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-·₁ t⟶s) (ξ-·₁ t⟶u) = cong (_· _) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-·₂ _ t⟶s) (ξ-·₂ _ t⟶u) = cong (_ ·_) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-delimit t⟶s) (ξ-delimit t⟶u) = cong delimit (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-case t⟶s) (ξ-case t⟶u) = cong (case _ _) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (β-ƛ v) (ξ-·₂ _ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
-- ⟶-deterministic (ξ-·₂ _ t⟶s) (β-ƛ v) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (β-delimit₁ v) (ξ-delimit t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
-- ⟶-deterministic (ξ-delimit t⟶s) (β-delimit₁ v) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (β-delimit₁ v) (β-delimit₂ c) = ⊥-elim (V¬⟨grab⟩ v c)
-- ⟶-deterministic (β-delimit₂ c) (β-delimit₁ v) = ⊥-elim (V¬⟨grab⟩ v c)
-- ⟶-deterministic (β-delimit₂ c) (ξ-delimit t⟶u) = ⊥-elim (⟨grab⟩¬⟶ c t⟶u)
-- ⟶-deterministic (ξ-delimit t⟶s) (β-delimit₂ c) = ⊥-elim (⟨grab⟩¬⟶ c t⟶s)
-- ⟶-deterministic (β-suc v) (ξ-case t⟶u) = ⊥-elim (V¬⟶ (suc v) t⟶u)
-- ⟶-deterministic (ξ-case t⟶s) (β-suc v) = ⊥-elim (V¬⟶ (suc v) t⟶s)
-- ⟶-deterministic (ξ-·₁ t⟶s) (ξ-·₂ v t⟶u) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (ξ-·₂ v t⟶s) (ξ-·₁ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
