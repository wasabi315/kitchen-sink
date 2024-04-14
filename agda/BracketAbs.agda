-- Ref: https://okmij.org/ftp/tagless-final/ski.pdf

module BracketAbs where

open import Data.Empty using ( ⊥ )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function.Base using ( id; const; flip; _∘′_; _ˢ_; _$_ )
open import Function.Definitions using ( Injective )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using ( True; toWitness )

--------------------------------------------------------------------------------
-- Misc

cong-app₂ : ∀ {A B C : Set} {f g : A → B → C}
  → f ≡ g
  → ∀ x y → f x y ≡ g x y
cong-app₂ refl x y = refl

--------------------------------------------------------------------------------
-- STLC

infixr 7 _⇒_
infixl 5 _,_

data Ty : Set where
  ι : Ty
  _⇒_ : (α β : Ty) → Ty

data Ctx : Set where
  ∙ : Ctx
  _,_ : (Γ : Ctx) (α : Ty) → Ctx

length : Ctx → ℕ
length ∙ = zero
length (ctx , _) = suc (length ctx)

private
  variable
    Γ : Ctx
    α β γ : Ty

infix 4 _∋_
infix 5 ƛ_
infixl 7 _·_

data _∋_ : Ctx → Ty → Set where
  zero : Γ , α ∋ α
  suc : Γ ∋ α → Γ , β ∋ α

data Term : Ctx → Ty → Set where
  var : Γ ∋ α → Term Γ α
  ƛ_ : (t : Term (Γ , α) β) → Term Γ (α ⇒ β)
  _·_ : (t : Term Γ (α ⇒ β)) (s : Term Γ α) → Term Γ β

infix 9 #_

lookupCtx : ∀ {Γ n} (p : n < length Γ) → Ty
lookupCtx {Γ , α} {zero} p = α
lookupCtx {Γ , α} {suc n} (s≤s p) = lookupCtx p

ℕ-to-index : ∀ {Γ n} (p : n < length Γ) → Γ ∋ lookupCtx p
ℕ-to-index {Γ , α} {zero} p = zero
ℕ-to-index {Γ , α} {suc n} (s≤s p) = suc (ℕ-to-index p)

#_ : ∀ {Γ} n {n∈Γ : True (suc n ≤? length Γ)}
  → Term Γ (lookupCtx (toWitness n∈Γ))
#_ n {n∈Γ} = var (ℕ-to-index (toWitness n∈Γ))

`id : Term ∙ (α ⇒ α)
`id = ƛ # 0

`const : Term ∙ (α ⇒ β ⇒ α)
`const = ƛ ƛ # 1

`ap : Term ∙ ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
`ap = ƛ ƛ ƛ # 2 · # 0 · (# 1 · # 0)

`compose : Term ∙ ((β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
`compose = ƛ ƛ ƛ # 2 · (# 1 · # 0)

`flip : Term ∙ ((α ⇒ β ⇒ γ) ⇒ β ⇒ α ⇒ γ)
`flip = ƛ ƛ ƛ # 2 · # 0 · # 1

--------------------------------------------------------------------------------
-- Evaluation

⟦_⟧ᵗ : Ty → Set
⟦ ι ⟧ᵗ = ⊥
⟦ α ⇒ β ⟧ᵗ = ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ

data ⟦_⟧ᶜ : Ctx → Set where
  ∙ : ⟦ ∙ ⟧ᶜ
  _,_ : (e : ⟦ Γ ⟧ᶜ) (x : ⟦ α ⟧ᵗ) → ⟦ Γ , α ⟧ᶜ

lookup : ⟦ Γ ⟧ᶜ → Γ ∋ α → ⟦ α ⟧ᵗ
lookup (e , x) zero = x
lookup (e , _) (suc i) = lookup e i

⟦_⟧′ : Term Γ α → ⟦ Γ ⟧ᶜ → ⟦ α ⟧ᵗ
⟦ var i ⟧′ e = lookup e i
⟦ ƛ t ⟧′ e x = ⟦ t ⟧′ (e , x)
⟦ t · s ⟧′ e = ⟦ t ⟧′ e (⟦ s ⟧′ e)

⟦_⟧ : Term ∙ α → ⟦ α ⟧ᵗ
⟦_⟧ t = ⟦ t ⟧′ ∙

--------------------------------------------------------------------------------
-- Combinators

data SKI : Ty → Set where
  I : SKI (α ⇒ α)
  K : SKI (α ⇒ β ⇒ α)
  S : SKI ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  B : SKI ((β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  C : SKI ((α ⇒ β ⇒ γ) ⇒ β ⇒ α ⇒ γ)
  _·_ : (t : SKI (α ⇒ β)) (s : SKI α) → SKI β

⟦_⟧ˢ : SKI α → ⟦ α ⟧ᵗ
⟦ I ⟧ˢ = id
⟦ K ⟧ˢ = const
⟦ S ⟧ˢ = _ˢ_
⟦ B ⟧ˢ = _∘′_
⟦ C ⟧ˢ = flip
⟦ t · s ⟧ˢ = ⟦ t ⟧ˢ ⟦ s ⟧ˢ

·-injective₁ : {t : SKI (α ⇒ β)} {s : SKI α} {t′ : SKI (α ⇒ β)} {s′ : SKI α}
  → t · s ≡ t′ · s′
  → t ≡ t′
·-injective₁ refl = refl

·-injective₂ : ∀ {t : SKI (α ⇒ β)} {s : SKI α} {t′ : SKI (α ⇒ β)} {s′ : SKI α}
  → t · s ≡ t′ · s′
  → s ≡ s′
·-injective₂ refl = refl

--------------------------------------------------------------------------------
-- Bracket abstraction

data BTerm : Ctx → Ty → Set where
  -- C: Already converted
  done : (t : SKI α) → BTerm Γ α
  -- V: A reference to the topmost variable in the context
  top : BTerm (Γ , α) α
  -- N: Apply a function `t` to the topmost variable in the context
  use-top : (t : BTerm Γ (α ⇒ β)) → BTerm (Γ , α) β
  -- W: Ignore the topmost variable in the context
  ignore-top : (t : BTerm Γ β) → BTerm (Γ , α) β

⟦_⟧ᵇ : BTerm Γ α → ⟦ Γ ⟧ᶜ → ⟦ α ⟧ᵗ
⟦ done t ⟧ᵇ e = ⟦ t ⟧ˢ
⟦ top ⟧ᵇ (e , x) = x
⟦ use-top t ⟧ᵇ (e , x) = ⟦ t ⟧ᵇ e x
⟦ ignore-top t ⟧ᵇ (e , x) = ⟦ t ⟧ᵇ e

infixl 5 _$$_

_$$_ : BTerm Γ (α ⇒ β) → BTerm Γ α → BTerm Γ β
done t       $$ done s       = done (t · s)
done t       $$ top          = use-top (done t)
done t       $$ use-top s    = use-top (done (B · t) $$ s)
done t       $$ ignore-top s = ignore-top (done t $$ s)
top          $$ done t       = use-top (done (C · I · t))
top          $$ use-top s    = use-top (done (S · I) $$ s)
top          $$ ignore-top s = use-top (done (C · I) $$ s)
use-top t    $$ done s       = use-top (done (C · C · s) $$ t)
use-top t    $$ top          = use-top (done S $$ t $$ done I)
use-top t    $$ use-top s    = use-top (done S $$ t $$ s)
use-top t    $$ ignore-top s = use-top (done C $$ t $$ s)
ignore-top t $$ done s       = ignore-top (t $$ done s)
ignore-top t $$ top          = use-top t
ignore-top t $$ use-top s    = use-top (done B $$ t $$ s)
ignore-top t $$ ignore-top s = ignore-top (t $$ s)

bracket-var : Γ ∋ α → BTerm Γ α
bracket-var zero = top
bracket-var (suc i) = ignore-top (bracket-var i)

bracket-ƛ : BTerm (Γ , α) β → BTerm Γ (α ⇒ β)
bracket-ƛ (done t) = done (K · t)
bracket-ƛ top = done I
bracket-ƛ (use-top t) = t
bracket-ƛ (ignore-top t) = done K $$ t

bracket′ : Term Γ α → BTerm Γ α
bracket′ (var i) = bracket-var i
bracket′ (ƛ t) = bracket-ƛ (bracket′ t)
bracket′ (t · s) = bracket′ t $$ bracket′ s

-- Bracket abstraction preserves the typing by construction
bracket : Term ∙ α → SKI α
bracket t with done s ← bracket′ t = s

bracket⁻ : SKI α → Term ∙ α
bracket⁻ I = `id
bracket⁻ K = `const
bracket⁻ S = `ap
bracket⁻ B = `compose
bracket⁻ C = `flip
bracket⁻ (t · s) = bracket⁻ t · bracket⁻ s

--------------------------------------------------------------------------------
-- Bracket abstraction preserves the semantics

⟦-⟧-bracket⁻ : ∀ (t : SKI α) → ⟦ bracket⁻ t ⟧ ≡ ⟦ t ⟧ˢ
⟦-⟧-bracket⁻ I = refl
⟦-⟧-bracket⁻ K = refl
⟦-⟧-bracket⁻ S = refl
⟦-⟧-bracket⁻ B = refl
⟦-⟧-bracket⁻ C = refl
⟦-⟧-bracket⁻ (t · s) = cong₂ _$_ (⟦-⟧-bracket⁻ t) (⟦-⟧-bracket⁻ s)

module _ where
  open ≡-Reasoning

  ⟦-⟧ᵇ-$$ : ∀ (t : BTerm Γ (α ⇒ β)) s e
    → ⟦ t $$ s ⟧ᵇ e ≡ ⟦ t ⟧ᵇ e (⟦ s ⟧ᵇ e)
  ⟦-⟧ᵇ-$$ (done t) (done s) e = refl
  ⟦-⟧ᵇ-$$ (done t) top (e , x) = refl
  ⟦-⟧ᵇ-$$ (done t) (use-top s) (e , x) =
    cong-app (⟦-⟧ᵇ-$$ (done (B · t)) s e) x
  ⟦-⟧ᵇ-$$ (done t) (ignore-top s) (e , x) =
    ⟦-⟧ᵇ-$$ (done t) s e
  ⟦-⟧ᵇ-$$ top (done t) (e , x) = refl
  ⟦-⟧ᵇ-$$ top (use-top s) (e , x) =
    cong-app (⟦-⟧ᵇ-$$ (done (S · I)) s e) x
  ⟦-⟧ᵇ-$$ top (ignore-top s) (e , x) =
    cong-app (⟦-⟧ᵇ-$$ (done (C · I)) s e) x
  ⟦-⟧ᵇ-$$ (use-top t) (done s) (e , x) =
    cong-app (⟦-⟧ᵇ-$$ (done (C · C · s)) t e) x
  ⟦-⟧ᵇ-$$ (use-top t) top (e , x) = begin
      ⟦ done S $$ t $$ done I ⟧ᵇ e x
    ≡⟨ cong-app (⟦-⟧ᵇ-$$ (done S $$ t) (done I) e) x ⟩
      ⟦ done S $$ t ⟧ᵇ e id x
    ≡⟨ cong-app₂ (⟦-⟧ᵇ-$$ (done S) t e) id x ⟩
      ⟦ t ⟧ᵇ e x x
    ∎
  ⟦-⟧ᵇ-$$ (use-top t) (use-top s) (e , x) = begin
      ⟦ done S $$ t $$ s ⟧ᵇ e x
    ≡⟨ cong-app (⟦-⟧ᵇ-$$ (done S $$ t) s e) x ⟩
      ⟦ done S $$ t ⟧ᵇ e (⟦ s ⟧ᵇ e) x
    ≡⟨ cong-app₂ (⟦-⟧ᵇ-$$ (done S) t e) (⟦ s ⟧ᵇ e) x ⟩
      ⟦ t ⟧ᵇ e x (⟦ s ⟧ᵇ e x)
    ∎
  ⟦-⟧ᵇ-$$ (use-top t) (ignore-top s) (e , x) = begin
      ⟦ done C $$ t $$ s ⟧ᵇ e x
    ≡⟨ cong-app (⟦-⟧ᵇ-$$ (done C $$ t) s e) x ⟩
      ⟦ done C $$ t ⟧ᵇ e (⟦ s ⟧ᵇ e) x
    ≡⟨ cong-app₂ (⟦-⟧ᵇ-$$ (done C) t e) _ x ⟩
      ⟦ t ⟧ᵇ e x (⟦ s ⟧ᵇ e)
    ∎
  ⟦-⟧ᵇ-$$ (ignore-top t) (done s) (e , x) =
    ⟦-⟧ᵇ-$$ t (done s) e
  ⟦-⟧ᵇ-$$ (ignore-top t) top (e , x) = refl
  ⟦-⟧ᵇ-$$ (ignore-top t) (use-top s) (e , x) = begin
      ⟦ done B $$ t $$ s ⟧ᵇ e x
    ≡⟨ cong-app (⟦-⟧ᵇ-$$ (done B $$ t) s e) x ⟩
      ⟦ done B $$ t ⟧ᵇ e (⟦ s ⟧ᵇ e) x
    ≡⟨ cong-app₂ (⟦-⟧ᵇ-$$ (done B) t e) _ x ⟩
      ⟦ t ⟧ᵇ e (⟦ s ⟧ᵇ e x)
    ∎
  ⟦-⟧ᵇ-$$ (ignore-top t) (ignore-top s) (e , x) =
    ⟦-⟧ᵇ-$$ t s e

  ⟦-⟧ᵇ-bracket-var : ∀ (i : Γ ∋ α) e → ⟦ bracket-var i ⟧ᵇ e ≡ lookup e i
  ⟦-⟧ᵇ-bracket-var zero (e , x) = refl
  ⟦-⟧ᵇ-bracket-var (suc i) (e , x) = ⟦-⟧ᵇ-bracket-var i e

  ⟦-⟧ᵇ-bracket-ƛ : ∀ (t : BTerm (Γ , α) β) e
    → ⟦ bracket-ƛ t ⟧ᵇ e ≡ (λ x → ⟦ t ⟧ᵇ (e , x))
  ⟦-⟧ᵇ-bracket-ƛ (done t) e = refl
  ⟦-⟧ᵇ-bracket-ƛ top e = refl
  ⟦-⟧ᵇ-bracket-ƛ (use-top t) e =  refl
  ⟦-⟧ᵇ-bracket-ƛ (ignore-top t) e = ⟦-⟧ᵇ-$$ (done K) t e

  open import Axiom.Extensionality.Propositional

  -- How to get rid of this assumption?
  module _ (funExt : Extensionality _ _) where

    ⟦-⟧ᵇ-bracket′ : ∀ (t : Term Γ α) e → ⟦ bracket′ t ⟧ᵇ e ≡ ⟦ t ⟧′ e
    ⟦-⟧ᵇ-bracket′ (var i) e = ⟦-⟧ᵇ-bracket-var i e
    ⟦-⟧ᵇ-bracket′ (ƛ t) e = begin
        ⟦ bracket-ƛ (bracket′ t) ⟧ᵇ e
      ≡⟨ ⟦-⟧ᵇ-bracket-ƛ (bracket′ t) e ⟩
        (λ x → ⟦ bracket′ t ⟧ᵇ (e , x))
      ≡⟨ funExt (λ x → ⟦-⟧ᵇ-bracket′ t (e , x)) ⟩
        (λ x → ⟦ t ⟧′ (e , x))
      ∎
    ⟦-⟧ᵇ-bracket′ (t · s) e = begin
        ⟦ bracket′ t $$ bracket′ s ⟧ᵇ e
      ≡⟨ ⟦-⟧ᵇ-$$ (bracket′ t) (bracket′ s) e ⟩
        ⟦ bracket′ t ⟧ᵇ e (⟦ bracket′ s ⟧ᵇ e)
      ≡⟨ cong₂ _$_ (⟦-⟧ᵇ-bracket′ t e) (⟦-⟧ᵇ-bracket′ s e) ⟩
        ⟦ t ⟧′ e (⟦ s ⟧′ e)
      ∎

    ⟦-⟧ˢ-bracket : ∀ (t : Term ∙ α) → ⟦ bracket t ⟧ˢ ≡ ⟦ t ⟧
    ⟦-⟧ˢ-bracket t with bracket′ t | ⟦-⟧ᵇ-bracket′ t ∙
    ... | done s | eq = eq

    bracket⁻-bracket : ∀ (t : Term ∙ α) → ⟦ bracket⁻ (bracket t) ⟧ ≡ ⟦ t ⟧
    bracket⁻-bracket t = trans (⟦-⟧-bracket⁻ (bracket t)) (⟦-⟧ˢ-bracket t)

--------------------------------------------------------------------------------
-- Stability

bracket′-bracket⁻ : ∀ (t : SKI α) → bracket′ (bracket⁻ t) ≡ done t
bracket′-bracket⁻ I = refl
bracket′-bracket⁻ K = refl
bracket′-bracket⁻ S = refl
bracket′-bracket⁻ B = refl
bracket′-bracket⁻ C = refl
bracket′-bracket⁻ (t · u)
  rewrite bracket′-bracket⁻ t | bracket′-bracket⁻ u = refl

bracket-bracket⁻ : ∀ (t : SKI α) → bracket (bracket⁻ t) ≡ t
bracket-bracket⁻ t with bracket′ (bracket⁻ t) | bracket′-bracket⁻ t
... | done .t | refl = refl

--------------------------------------------------------------------------------

church : ℕ → Term Γ ((α ⇒ α) ⇒ α ⇒ α)
church zero = ƛ ƛ # 0
church (suc n) = ƛ ƛ # 1 · (church n · # 1 · # 0)

_ : bracket (church {α = α} 0) ≡ K · I
_ = refl

_ : bracket (church {α = α} 1) ≡ S · B · (K · I)
_ = refl

_ : bracket (church {α = α} 2) ≡ S · B · (S · B · (K · I))
_ = refl
