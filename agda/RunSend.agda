module RunSend where

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function using ( flip; _$_; _∘′_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using ( Star; ε; _◅_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning )
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
  _➡_ : Ty → Ty → Eff

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Ty → Ctx

private
  variable
    Γ Δ : Ctx
    α β γ αₕ βₕ : Ty
    E E' Eₕ : Eff

data _∋_ : Ctx → Ty → Set where
  zero : Γ , α ∋ α
  suc : Γ ∋ α → Γ , β ∋ α

data Term : Ctx → Eff → Ty → Set where
  var : Γ ∋ α → Term Γ E α
  ƛ_ : Term (Γ , α) E β → Term Γ E' (α ⇒ β ! E)
  _·_ : Term Γ E (α ⇒ β ! E) → Term Γ E α → Term Γ E β
  send : Term Γ (α ➡ β) α → Term Γ (α ➡ β) β
  run : Term Γ (α ➡ β) γ → Term (Γ , α , β ⇒ γ ! E) E γ → Term Γ E γ
  zero : Term Γ E `ℕ
  suc : Term Γ E `ℕ → Term Γ E `ℕ
  case : Term Γ E α → Term (Γ , `ℕ) E α → Term Γ E `ℕ → Term Γ E α

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

-- run (suc (send 0)) (x k. k (k x))
ex : Term ∅ ι `ℕ
ex = run (suc (send zero)) (# 0 · (# 0 · # 1))

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
rename ρ (send t) = send (rename ρ t)
rename ρ (run t u) = run (rename ρ t) (rename (ext (ext ρ)) u)
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
subst σ (send t) = send (subst σ t)
subst σ (run t u) = run (subst σ t) (subst (exts (exts σ)) u)
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
  send : {t : Term Γ (α ➡ β) α}
    → InCtx h t
    → InCtx h (send t)
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
send c ⟨ u ⟩ = send (c ⟨ u ⟩)
suc c ⟨ u ⟩ = suc (c ⟨ u ⟩)
case s t c ⟨ u ⟩ = case s t (c ⟨ u ⟩)

rename⟨⟩ : (ρ : Rename Γ Δ) {h : Term Γ E α} {t : Term Γ E' β}
  → (c : InCtx h t)
  → InCtx (rename ρ h) (rename ρ t)
rename⟨⟩ ρ ⟨⟩ = ⟨⟩
rename⟨⟩ ρ (c ·₁ u) = rename⟨⟩ ρ c ·₁ rename ρ u
rename⟨⟩ ρ (v ·₂ c) = renameV ρ v ·₂ rename⟨⟩ ρ c
rename⟨⟩ ρ (send c) = send (rename⟨⟩ ρ c)
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

  β-run₁ : {t : Term Γ (α ➡ β) γ} {u : Term (Γ , α , β ⇒ γ ! E) E γ}
    → (v : Value t)
    → run t u ⟶ coe v

  β-run₂ : {s : Term Γ (α ➡ β) γ} {t : Term Γ (α ➡ β) α} {u : Term (Γ , α , β ⇒ γ ! E) E γ}
    → (c : InCtx (send t) s)
    → (v : Value t)
    → run s u ⟶ ((u [ ƛ run (↑⟨⟩ (↑⟨⟩ c) ⟨ # 0 ⟩) (rename (ext (ext (suc ∘′ suc))) u) ]) [ coe v ])

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

  ξ-send : {t t' : Term Γ (α ➡ β) α}
    → t ⟶ t'
    → send t ⟶ send t'

  ξ-run : {t t' : Term Γ (α ➡ β) γ} {u : Term (Γ , α , β ⇒ γ ! E) E γ}
    → t ⟶ t'
    → run t u ⟶ run t' u

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
    run (suc (send zero)) (# 0 · (# 0 · # 1))
  ⟶⟨ β-run₂ (suc ⟨⟩) zero ⟩
    ((# 0 · (# 0 · # 1)) [ ƛ run (suc (# 0)) (# 0 · (# 0 · # 1)) ]) [ zero ]
  ≡⟨⟩
    (ƛ run (suc (# 0)) (# 0 · (# 0 · # 1))) · ((ƛ run (suc (# 0)) (# 0 · (# 0 · # 1))) · zero)
  ⟶⟨ ξ-·₂ (ƛ run (suc (# 0)) (# 0 · (# 0 · # 1))) (β-ƛ zero) ⟩
    (ƛ run (suc (# 0)) (# 0 · (# 0 · # 1))) · (run (suc zero) (# 0 · (# 0 · # 1)))
  ⟶⟨ ξ-·₂ (ƛ run (suc (# 0)) (# 0 · (# 0 · # 1))) (β-run₁ (suc zero)) ⟩
    (ƛ run (suc (# 0)) (# 0 · (# 0 · # 1))) · (suc zero)
  ⟶⟨ β-ƛ (suc zero) ⟩
    run (suc (suc zero)) (# 0 · (# 0 · # 1))
  ⟶⟨ β-run₁ (suc (suc zero)) ⟩
    suc (suc zero)
  ∎
  where open ⟶*-Reasoning

--------------------------------------------------------------------------------
-- Soundness
-- Preservation holds by construction.

data Progress : Term ∅ E α → Set where
  done : {t : Term ∅ E α} → Value t → Progress t
  step : {t t' : Term ∅ E α} → t ⟶ t' → Progress t
  bare-send : {t : Term ∅ (α ➡ β) γ} {u : Term ∅ (α ➡ β) α}
    → Value u
    → InCtx (send u) t
    → Progress t

progress : (t : Term ∅ E α) → Progress t
progress (ƛ t) = done (ƛ t)
progress (t · u) with progress t
... | step t⟶t' = step (ξ-·₁ t⟶t')
... | bare-send v c = bare-send v (c ·₁ u)
... | done (ƛ t') with progress u
...   | step u⟶u' = step (ξ-·₂ (ƛ t') u⟶u')
...   | bare-send v c = bare-send v ((ƛ t') ·₂ c)
...   | done vu = step (β-ƛ vu)
progress (send t) with progress t
... | step t⟶t' = step (ξ-send t⟶t')
... | done vt = bare-send vt ⟨⟩
... | bare-send v c = bare-send v (send c)
progress (run t u) with progress t
... | step t⟶t' = step (ξ-run t⟶t')
... | done vt = step (β-run₁ vt)
... | bare-send v c = step (β-run₂ c v)
progress zero = done zero
progress (suc t) with progress t
... | step t⟶t' = step (ξ-suc t⟶t')
... | done vt = done (suc vt)
... | bare-send v c = bare-send v (suc c)
progress (case s t u) with progress u
... | step u⟶u' = step (ξ-case u⟶u')
... | done zero = step β-zero
... | done (suc vu) = step (β-suc vu)
... | bare-send v c = bare-send v (case s t c)

--------------------------------------------------------------------------------

V¬⟶ : {v v' : Term Γ E α} → Value v → ¬ (v ⟶ v')
V¬⟶ (suc v) (ξ-suc v⟶v') = V¬⟶ v v⟶v'

V-unique : {t : Term Γ E α} (v v' : Value t) → v ≡ v'
V-unique (ƛ t) (ƛ .t) = refl
V-unique zero zero = refl
V-unique (suc v) (suc v') = cong suc (V-unique v v')

V¬⟨send⟩ : {t : Term Γ E α} {u : Term Γ (β ➡ γ) β}
  → Value t
  → ¬ InCtx (send u) t
V¬⟨send⟩ (suc v) (suc c) = V¬⟨send⟩ v c

⟨send⟩¬⟶ : {u : Term Γ (α ➡ β) α} {t t' : Term Γ E γ}
  → Value u
  → InCtx (send u) t
  → ¬ (t ⟶ t')
⟨send⟩¬⟶ v ⟨⟩ (ξ-send t⟶t') = V¬⟶ v t⟶t'
⟨send⟩¬⟶ v (c ·₁ u) (ξ-·₁ t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
⟨send⟩¬⟶ v (c ·₁ u) (ξ-·₂ v' t⟶t') = ⊥-elim (V¬⟨send⟩ v' c)
⟨send⟩¬⟶ v (v' ·₂ c) (β-ƛ v'') = ⊥-elim (V¬⟨send⟩ v'' c)
⟨send⟩¬⟶ v (v' ·₂ c) (ξ-·₁ t⟶t') = ⊥-elim (V¬⟶ v' t⟶t')
⟨send⟩¬⟶ v (v' ·₂ c) (ξ-·₂ v'' t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
⟨send⟩¬⟶ v (send c) (ξ-send t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
⟨send⟩¬⟶ v (suc c) (ξ-suc t⟶t') = ⟨send⟩¬⟶ v c t⟶t'
⟨send⟩¬⟶ v (case s t c) (β-suc v') = ⊥-elim (V¬⟨send⟩ (suc v') c)
⟨send⟩¬⟶ v (case s t c) (ξ-case t⟶t') = ⟨send⟩¬⟶ v c t⟶t'

-- ⟶-deterministic : {t s u : Term Γ E α} → t ⟶ s → t ⟶ u → s ≡ u
-- ⟶-deterministic (β-ƛ {t = t} v) (β-ƛ v') = cong (λ u → t [ coe u ]) (V-unique v v')
-- ⟶-deterministic (β-run₁ v) (β-run₁ v') = cong coe (V-unique v v')
-- ⟶-deterministic (β-run₂ c v) (β-run₂ c' v') = {!   !}
-- ⟶-deterministic β-zero β-zero = refl
-- ⟶-deterministic (β-suc {u = t} v) (β-suc v') = cong (λ u → t [ coe u ]) (V-unique v v')
-- ⟶-deterministic (ξ-·₁ t⟶s) (ξ-·₁ t⟶u) = cong (_· _) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-·₂ _ t⟶s) (ξ-·₂ _ t⟶u) = cong (_ ·_) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-send t⟶s) (ξ-send t⟶u) = cong send (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-run {u = u} t⟶s) (ξ-run t⟶u) = cong (flip run u) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-suc t⟶s) (ξ-suc t⟶u) = cong suc (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (ξ-case t⟶s) (ξ-case t⟶u) = cong (case _ _) (⟶-deterministic t⟶s t⟶u)
-- ⟶-deterministic (β-ƛ v) (ξ-·₂ _ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
-- ⟶-deterministic (ξ-·₂ _ t⟶s) (β-ƛ v) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (β-run₁ v) (β-run₂ c _) = ⊥-elim (V¬⟨send⟩ v c)
-- ⟶-deterministic (β-run₂ c _) (β-run₁ v) = ⊥-elim (V¬⟨send⟩ v c)
-- ⟶-deterministic (β-run₁ v) (ξ-run t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
-- ⟶-deterministic (ξ-run t⟶s) (β-run₁ v) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (β-run₂ c v) (ξ-run t⟶u) = ⊥-elim (⟨send⟩¬⟶ v c t⟶u)
-- ⟶-deterministic (ξ-run t⟶s) (β-run₂ c v) = ⊥-elim (⟨send⟩¬⟶ v c t⟶s)
-- ⟶-deterministic (β-suc v) (ξ-case t⟶u) = ⊥-elim (V¬⟶ (suc v) t⟶u)
-- ⟶-deterministic (ξ-case t⟶s) (β-suc v) = ⊥-elim (V¬⟶ (suc v) t⟶s)
-- ⟶-deterministic (ξ-·₁ t⟶s) (ξ-·₂ v t⟶u) = ⊥-elim (V¬⟶ v t⟶s)
-- ⟶-deterministic (ξ-·₂ v t⟶s) (ξ-·₁ t⟶u) = ⊥-elim (V¬⟶ v t⟶u)
