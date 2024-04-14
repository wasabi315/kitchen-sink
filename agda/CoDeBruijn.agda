-- Ref: https://jesper.sikanda.be/posts/1001-syntax-representations.html#co-de-bruijn-indices

module CoDeBruijn where

open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product using ( _×_ ) renaming ( _,_ to _,,_ )

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
infixl 5 _keep_ _drop_
data _⊑_ : Scope → Scope → Set where
  ∅ : ∅ ⊑ ∅
  _keep_ : (p : Γ ⊑ Δ) (α : Type) → Γ , α ⊑ Δ , α
  _drop_ : (p : Γ ⊑ Δ) (α : Type) → Γ ⊑ Δ , α

data Cover : (p : Γ ⊑ Σ) (q : Δ ⊑ Σ) → Set where
  ∅ : Cover ∅ ∅
  _L : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Cover (p keep α) (q drop α)
  _R : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Cover (p drop α) (q keep α)
  _B : {p : Γ ⊑ Σ} {q : Δ ⊑ Σ}
    → Cover p q
    → Cover (p keep α) (q keep α)

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

-- TODO: Bracket abstraction for lambda terms with co-de Bruijn indices?
