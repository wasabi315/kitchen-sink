-- Ref: https://jesper.sikanda.be/posts/1001-syntax-representations.html#co-de-bruijn-indices

module CoDeBruijn where

open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

private
  variable
    V W X Y Z : Set
    l m n : ℕ

--------------------------------------------------------------------------------
-- Syntax

infixr 7 _⇒_
data Type : Set where
  ι : Type
  _⇒_ : (α β : Type) → Type

infixl 5 _,_
data Scope : Set where
  ∅ : Scope
  _,_ : (Γ : Scope) (α : Type) → Scope

private
  variable
    α β γ : Type
    Γ Δ Σ : Scope

infix 4 _⊑_
infix 5 _keep_ _drop_
data _⊑_ : Scope → Scope → Set where
  ∅ : ∅ ⊑ ∅
  _keep_ : (p : Γ ⊑ Δ) (α : Type) → Γ , α ⊑ Δ , α
  _drop_ : (p : Γ ⊑ Δ) (α : Type) → Γ ⊑ Δ , α

data Cover : (p : Γ ⊑ Σ) (q : Δ ⊑ Σ) → Set where
  ∅ : Cover ∅ ∅
  _L : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Cover (p keep α) (q drop α) -- C
  _R : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Cover (p drop α) (q keep α) -- B
  _B : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Cover (p keep α) (q keep α) -- S

infix 5 ƛ_ ƛ-_

data Term : (Γ : Scope) (α : Type) → Set where
  var : Term (∅ , α) α
  ƛ_ : Term (Γ , α) β → Term Γ (α ⇒ β)
  ƛ-_ : Term Γ α → Term Γ (β ⇒ α)
  app : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Term Γ (α ⇒ β)
    → Term Δ α
    → Term Σ β

--------------------------------------------------------------------------------

`I : Term ∅ (α ⇒ α)
`I = ƛ var
--   x  x

`K : Term ∅ (α ⇒ β ⇒ α)
`K = ƛ ƛ- var
--   x _   x

`S : Term ∅ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
`S = ƛ ƛ ƛ app (∅ L R B) (app (∅ L R) var var) (app (∅ L R) var var)
--   f g x        f g x          f x   f   x           g x   g   x

`B : Term ∅ ((α ⇒ β) ⇒ (γ ⇒ α) ⇒ γ ⇒ β)
`B = ƛ ƛ ƛ app (∅ L R R) var (app (∅ L R) var var)
--   f g x        f g x   f          g x   g   x

`C : Term ∅ ((α ⇒ β ⇒ γ) ⇒ β ⇒ α ⇒ γ)
`C = ƛ ƛ ƛ app (∅ L R L) (app (∅ L R) var var) var
--   f x y        f x y          f y   f   y    x

church : (n : ℕ) → Term ∅ ((α ⇒ α) ⇒ α ⇒ α)
church zero = ƛ- ƛ var
church (suc n) = ƛ ƛ app (∅ B R) var (app (∅ L R) (app (∅ R) (church n) var) var)
--               s z        s z   s          s z          s              s    z

--------------------------------------------------------------------------------
-- Evaluation

Type⟦_⟧ : Type → Set
Type⟦ ι ⟧ = ⊥
Type⟦ t ⇒ u ⟧ = Type⟦ t ⟧ → Type⟦ u ⟧

data Scope⟦_⟧ : Scope → Set where
  ∅ : Scope⟦ ∅ ⟧
  _,_ : Scope⟦ Γ ⟧ → Type⟦ α ⟧ → Scope⟦ Γ , α ⟧

⊑⟦_⟧ : Γ ⊑ Δ → (Scope⟦ Δ ⟧ → Scope⟦ Γ ⟧)
⊑⟦ ∅ ⟧ s = s
⊑⟦ p keep α ⟧ (s , x) = ⊑⟦ p ⟧ s , x
⊑⟦ p drop α ⟧ (s , x) = ⊑⟦ p ⟧ s

Term⟦_⟧ : Term Γ α → (Scope⟦ Γ ⟧ → Type⟦ α ⟧)
Term⟦ var ⟧ (∅ , x) = x
Term⟦ ƛ t ⟧ s x = Term⟦ t ⟧ (s , x)
Term⟦ ƛ- t ⟧ s _ = Term⟦ t ⟧ s
Term⟦ app {p = p} {q} _ t u ⟧ s = Term⟦ t ⟧ (⊑⟦ p ⟧ s) (Term⟦ u ⟧ (⊑⟦ q ⟧ s))

--------------------------------------------------------------------------------
-- Bracket abstraction
-- There might be an efficient way to do bracket abstraction
-- since a term precisely knows in which subterms variables in scope are used.
-- I'm not sure how to do it in a type-preserving way yet.

infixl 7 _·_

data SKI : Type → Set where
  𝕀 : SKI (α ⇒ α)
  𝕂 : SKI (α ⇒ β ⇒ α)
  𝕊 : SKI ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  𝔹 : SKI ((β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  ℂ : SKI ((α ⇒ β ⇒ γ) ⇒ β ⇒ α ⇒ γ)
  _·_ : (t : SKI (α ⇒ β)) (u : SKI α) → SKI β

data BTerm : Scope → Type → Set where
  done : SKI α → BTerm Γ α
  var : BTerm (∅ , α) α
  use-top : BTerm Γ (α ⇒ β) → BTerm (Γ , α) β
  K·_ : BTerm Γ α → BTerm Γ (β ⇒ α)

bracket′ : Term Γ α → BTerm Γ α
bracket′ var = {!   !}
bracket′ (ƛ t) = {!   !}
bracket′ (ƛ- t) = K· bracket′ t
bracket′ (app x t u) = {!   !}

-- infixr 7 _*⇒_
-- _*⇒_ : Scope → Type → Type
-- ∅ *⇒ α = α
-- (Γ , α) *⇒ β = Γ *⇒ α ⇒ β

-- bracket-ƛ- : SKI (Γ *⇒ α) → SKI (Γ *⇒ β ⇒ α)
-- bracket-ƛ- {∅} t = 𝕂 · t
-- bracket-ƛ- {Γ , α} t = let t' = bracket-ƛ- {Γ} t in {!   !}

-- bracket-app : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
--   → Cover p q
--   → SKI (Γ *⇒ β ⇒ γ)
--   → SKI (Δ *⇒ β)
--   → SKI (Σ *⇒ γ)
-- bracket-app ∅ t u = t · u
-- bracket-app (c L) t u = {!   !}
-- bracket-app (c R) t u = {!   !}
-- bracket-app (c B) t u = {!   !}

-- bracket : Term Γ α → SKI (Γ *⇒ α)
-- bracket var = 𝕀
-- bracket (ƛ t) = bracket t
-- bracket (ƛ- t) = let t' = bracket t in {!   !}
-- bracket (app c t u) = bracket-app c (bracket t) (bracket u)
