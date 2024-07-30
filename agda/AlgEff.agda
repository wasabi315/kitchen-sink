module AlgEff where

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function using ( flip; _$_; _∘′_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star using ( Star; ε; _◅_ )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using ( module StarReasoning )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning )
  renaming ( subst to transport )
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ) renaming ( refl to hrefl )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable using ( True; toWitness )

--------------------------------------------------------------------------------

data BaseTy : Set where
  `ℕ : BaseTy

record Sig : Set₁ where
  field
    Op : Set
    Dom : Op → BaseTy
    Cod : Op → BaseTy

open Sig

module M (Σ : Sig) where

  infixr 7 _⇒_!_
  infix  4 _∋_ _∋ₑ_
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
    _,_ : Eff → Op Σ → Eff

  data Ctx : Set where
    ∅ : Ctx
    _,_ : Ctx → Ty → Ctx

  base : BaseTy → Ty
  base `ℕ = `ℕ

  private
    Dom' Cod' : Op Σ → Ty
    Dom' op = base (Dom Σ op)
    Cod' op = base (Cod Σ op)

  variable
    op op' : Op Σ
    Γ Δ : Ctx
    α β γ αₕ βₕ : Ty
    E E' Eₕ : Eff

  data _∋_ : Ctx → Ty → Set where
    zero : Γ , α ∋ α
    suc : Γ ∋ α → Γ , β ∋ α

  data _∋ₑ_ : Eff → Op Σ → Set where
    zero : E , op ∋ₑ op
    suc : E ∋ₑ op → E , op' ∋ₑ op

  data Term : Ctx → Eff → Ty → Set
  record Handler (Γ : Ctx) (E E' : Eff) (α β : Ty) : Set

  data Term where
    var : Γ ∋ α → Term Γ E α
    ƛ_ : Term (Γ , α) E β → Term Γ E' (α ⇒ β ! E)
    _·_ : Term Γ E (α ⇒ β ! E) → Term Γ E α → Term Γ E β
    perform : E ∋ₑ op → Term Γ E (Dom' op) → Term Γ E (Cod' op)
    handle : Term Γ E α → Handler Γ E E' α β → Term Γ E' β
    zero : Term Γ E `ℕ
    suc : Term Γ E `ℕ → Term Γ E `ℕ
    case : Term Γ E α → Term (Γ , `ℕ) E α → Term Γ E `ℕ → Term Γ E α

  record Handler Γ E E' α β where
    inductive
    no-eta-equality
    field
      valh : Term (Γ , α) E' β
      effh : E ∋ₑ op → Term (Γ , Dom' op , Cod' op ⇒ β ! E') E' β

  open Handler public

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

--------------------------------------------------------------------------------

  Rename : Ctx → Ctx → Set
  Rename Γ Δ = ∀ {α} → Γ ∋ α → Δ ∋ α

  ext : Rename Γ Δ → Rename (Γ , α) (Δ , α)
  ext ρ zero = zero
  ext ρ (suc i) = suc (ρ i)

  rename : Rename Γ Δ → Term Γ E α → Term Δ E α
  renameH : Rename Γ Δ → Handler Γ E E' α β → Handler Δ E E' α β

  rename ρ (var i) = var (ρ i)
  rename ρ (ƛ t) = ƛ rename (ext ρ) t
  rename ρ (t · u) = rename ρ t · rename ρ u
  rename ρ (perform op t) = perform op (rename ρ t)
  rename ρ (handle t h) = handle (rename ρ t) (renameH ρ h)
  rename ρ zero = zero
  rename ρ (suc t) = suc (rename ρ t)
  rename ρ (case s t u) = case (rename ρ s) (rename (ext ρ) t) (rename ρ u)

  valh (renameH ρ h) = rename (ext ρ) (valh h)
  effh (renameH ρ h) op = rename (ext (ext ρ)) (effh h op)

  ↑ : Term Γ E α → Term (Γ , β) E α
  ↑ = rename suc

--------------------------------------------------------------------------------

  Subst : Ctx → Ctx → Set
  Subst Γ Δ = ∀ {α} → Γ ∋ α → (∀ {E} → Term Δ E α)

  exts : Subst Γ Δ → Subst (Γ , α) (Δ , α)
  exts σ zero = var zero
  exts σ (suc i) = ↑ (σ i)

  subst : Subst Γ Δ → Term Γ E α → Term Δ E α
  substHandler : Subst Γ Δ → Handler Γ E E' α β → Handler Δ E E' α β

  subst σ (var i) = σ i
  subst σ (ƛ t) = ƛ subst (exts σ) t
  subst σ (t · u) = subst σ t · subst σ u
  subst σ (perform op t) = perform op (subst σ t)
  subst σ (handle t h) = handle (subst σ t) (substHandler σ h)
  subst σ zero = zero
  subst σ (suc t) = suc (subst σ t)
  subst σ (case s t u) = case (subst σ s) (subst (exts σ) t) (subst σ u)

  valh (substHandler σ h) = subst (exts σ) (valh h)
  effh (substHandler σ h) op = subst (exts (exts σ)) (effh h op)

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
    perform : (i : E ∋ₑ op) {t : Term Γ E (Dom' op)}
      → InCtx h t
      → InCtx h (perform i t)
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
  perform i c ⟨ u ⟩ = perform i (c ⟨ u ⟩)
  suc c ⟨ u ⟩ = suc (c ⟨ u ⟩)
  case s t c ⟨ u ⟩ = case s t (c ⟨ u ⟩)

  rename⟨⟩ : (ρ : Rename Γ Δ) {h : Term Γ E α} {t : Term Γ E' β}
    → (c : InCtx h t)
    → InCtx (rename ρ h) (rename ρ t)
  rename⟨⟩ ρ ⟨⟩ = ⟨⟩
  rename⟨⟩ ρ (c ·₁ u) = rename⟨⟩ ρ c ·₁ rename ρ u
  rename⟨⟩ ρ (v ·₂ c) = renameV ρ v ·₂ rename⟨⟩ ρ c
  rename⟨⟩ ρ (perform i c) = perform i (rename⟨⟩ ρ c)
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

    β-handle₁ : {t : Term Γ E α} {h : Handler Γ E E' α β}
      → (v : Value t)
      → handle t h ⟶ valh h [ coe v ]

    β-handle₂ : {i : E ∋ₑ op} {t : Term Γ E α} {u : Term Γ E (Dom' op)} {h : Handler Γ E E' α β}
      → (c : InCtx (perform i u) t)
      → (v : Value u)
      → handle t h ⟶ (effh h i [ ƛ handle (↑⟨⟩ (↑⟨⟩ c) ⟨ # 0 ⟩) (renameH (suc ∘′ suc) h) ]) [ coe v ]

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

    ξ-perform : {i : E ∋ₑ op} {t t' : Term Γ E (Dom' op)}
      → t ⟶ t'
      → perform i t ⟶ perform i t'

    ξ-handle : {t t' : Term Γ E α} {h : Handler Γ E E' α β}
      → t ⟶ t'
      → handle t h ⟶ handle t' h

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

--------------------------------------------------------------------------------
-- Soundness
-- Preservation holds by construction.

  data Progress : Term ∅ E α → Set where
    done : {t : Term ∅ E α} → Value t → Progress t
    step : {t t' : Term ∅ E α} → t ⟶ t' → Progress t
    bare-perform : {i : E ∋ₑ op} {t : Term ∅ E γ} {u : Term ∅ E (Dom' op)}
      → Value u
      → InCtx (perform i u) t
      → Progress t

  progress : (t : Term ∅ E α) → Progress t
  progress (ƛ t) = done (ƛ t)
  progress (t · u) with progress t
  ... | step t⟶t' = step (ξ-·₁ t⟶t')
  ... | bare-perform v c = bare-perform v (c ·₁ u)
  ... | done (ƛ t') with progress u
  ...   | step u⟶u' = step (ξ-·₂ (ƛ t') u⟶u')
  ...   | bare-perform v c = bare-perform v ((ƛ t') ·₂ c)
  ...   | done vu = step (β-ƛ vu)
  progress (perform i t) with progress t
  ... | step t⟶t' = step (ξ-perform t⟶t')
  ... | done vt = bare-perform vt ⟨⟩
  ... | bare-perform v c = bare-perform v (perform i c)
  progress (handle t h) with progress t
  ... | step t⟶t' = step (ξ-handle t⟶t')
  ... | done vt = step (β-handle₁ vt)
  ... | bare-perform v c = step (β-handle₂ c v)
  progress zero = done zero
  progress (suc t) with progress t
  ... | step t⟶t' = step (ξ-suc t⟶t')
  ... | done vt = done (suc vt)
  ... | bare-perform v c = bare-perform v (suc c)
  progress (case s t u) with progress u
  ... | step u⟶u' = step (ξ-case u⟶u')
  ... | done zero = step β-zero
  ... | done (suc vu) = step (β-suc vu)
  ... | bare-perform v c = bare-perform v (case s t c)

--------------------------------------------------------------------------------

data ExOp : Set where
  exOp : ExOp

exSig : Sig
Op exSig = ExOp
Dom exSig exOp = `ℕ
Cod exSig exOp = `ℕ

open M exSig

-- {return x. x} ⊎ {exOp x k. k (k x)}
exHandler : Handler ∅ (ι , exOp) ι `ℕ `ℕ
valh exHandler = # 0
effh exHandler zero = # 0 · (# 0 · # 1)

-- run (suc (perform exOp 0)) exHandler
ex : Term ∅ ι `ℕ
ex = handle (suc (perform zero zero)) exHandler

_ : ex ⟶* suc (suc zero)
_ =
  begin
    ex
  ≡⟨⟩
    handle (suc (perform zero zero)) exHandler
  ⟶⟨ β-handle₂ (suc ⟨⟩) zero ⟩
    (effh exHandler zero [ ƛ handle (suc (# 0)) (renameH (suc ∘′ suc) exHandler) ]) [ zero ]
  ≡⟨⟩
    (ƛ handle (suc (# 0)) _) · ((ƛ handle (suc (# 0)) _) · zero)
  ⟶⟨ ξ-·₂ (ƛ handle (suc (# 0)) _) (β-ƛ zero) ⟩
    (ƛ handle (suc (# 0)) _) · handle (suc zero) _
  ⟶⟨ ξ-·₂ (ƛ handle (suc (# 0)) _) (β-handle₁ (suc zero)) ⟩
    (ƛ handle (suc (# 0)) _) · suc zero
  ⟶⟨ β-ƛ (suc zero) ⟩
    handle (suc (suc zero)) _
  ⟶⟨ β-handle₁ (suc (suc zero)) ⟩
    suc (suc zero)
  ∎
  where open ⟶*-Reasoning
