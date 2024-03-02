-- Ref: https://okmij.org/ftp/tagless-final/ski.pdf

open import Data.Unit.Base using ( ⊤; tt )
open import Data.Nat using ( ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s )
open import Function.Base using ( id; const; flip; _∘′_; _ˢ_; _$_ )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using ( True; toWitness )

--------------------------------------------------------------------------------
-- Misc

cong-app₂ : ∀ {A B C : Set} {f g : A → B → C}
  → f ≡ g
  → ∀ x y → f x y ≡ g x y
cong-app₂ refl x y = refl

--------------------------------------------------------------------------------

infixr 7 _`→_
infixl 5 _,_

data Ty : Set where
  `⊤ : Ty
  _`→_ : (α β : Ty) → Ty

data Ctx : Set where
  ∙ : Ctx
  _,_ : (Γ : Ctx) (α : Ty) → Ctx

length : Ctx → ℕ
length ∙ = zero
length (ctx , _) = suc (length ctx)

private
  variable
    Γ Δ : Ctx
    α β γ : Ty

infix 4 _∋_
infix 5 ƛ_
infixl 7 _·_

data _∋_ : Ctx → Ty → Set where
  zero : Γ , α ∋ α
  suc : Γ ∋ α → Γ , β ∋ α

data Term : Ctx → Ty → Set where
  tt : Term Γ `⊤
  var : Γ ∋ α → Term Γ α
  ƛ_ : (t : Term (Γ , α) β) → Term Γ (α `→ β)
  _·_ : (t : Term Γ (α `→ β)) (s : Term Γ α) → Term Γ β

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

--------------------------------------------------------------------------------

⟦_⟧ᵗ : Ty → Set
⟦ `⊤ ⟧ᵗ = ⊤
⟦ α `→ β ⟧ᵗ = ⟦ α ⟧ᵗ → ⟦ β ⟧ᵗ

data Env : Ctx → Set where
  ∙ : Env ∙
  _,_ : Env Γ → ⟦ α ⟧ᵗ → Env (Γ , α)

lookupEnv : Env Γ → Γ ∋ α → ⟦ α ⟧ᵗ
lookupEnv (env , x) zero = x
lookupEnv (env , _) (suc i) = lookupEnv env i

⟦_⟧′ : Term Γ α → Env Γ → ⟦ α ⟧ᵗ
⟦ tt ⟧′ env = tt
⟦ var i ⟧′ env = lookupEnv env i
⟦ ƛ t ⟧′ env x = ⟦ t ⟧′ (env , x)
⟦ t · s ⟧′ env = ⟦ t ⟧′ env (⟦ s ⟧′ env)

⟦_⟧ : Term ∙ α → ⟦ α ⟧ᵗ
⟦_⟧ t = ⟦ t ⟧′ ∙

--------------------------------------------------------------------------------
-- Bracket abstraction

data SKI : Ty → Set where
  tt : SKI `⊤
  I : SKI (α `→ α)
  K : SKI (α `→ β `→ α)
  S : SKI ((α `→ β `→ γ) `→ (α `→ β) `→ α `→ γ)
  B : SKI ((β `→ γ) `→ (α `→ β) `→ α `→ γ)
  C : SKI ((α `→ β `→ γ) `→ β `→ α `→ γ)
  _·_ : (t : SKI (α `→ β)) (s : SKI α) → SKI β

⟦_⟧ˢ : SKI α → ⟦ α ⟧ᵗ
⟦ tt ⟧ˢ = tt
⟦ I ⟧ˢ = id
⟦ K ⟧ˢ = const
⟦ S ⟧ˢ = _ˢ_
⟦ B ⟧ˢ = _∘′_
⟦ C ⟧ˢ = flip
⟦ t · s ⟧ˢ = ⟦ t ⟧ˢ ⟦ s ⟧ˢ

data Conv : Ctx → Ty → Set where
  -- C: Already converted
  done : (t : SKI α) → Conv Γ α
  -- V: A reference to the topmost variable in the context
  top : Conv (Γ , α) α
  -- N: Apply a function `t` to the topmost variable in the context
  use-top : (t : Conv Γ (α `→ β)) → Conv (Γ , α) β
  -- W: Ignore the topmost variable in the context
  ignore-top : (t : Conv Γ β) → Conv (Γ , α) β

⟦_⟧ᶜ : Conv Γ α → Env Γ → ⟦ α ⟧ᵗ
⟦ done t ⟧ᶜ env = ⟦ t ⟧ˢ
⟦ top ⟧ᶜ (env , x) = x
⟦ use-top t ⟧ᶜ (env , x) = ⟦ t ⟧ᶜ env x
⟦ ignore-top t ⟧ᶜ (env , x) = ⟦ t ⟧ᶜ env

infixl 5 _$$_

_$$_ : Conv Γ (α `→ β) → Conv Γ α → Conv Γ β
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

bracket-var : Γ ∋ α → Conv Γ α
bracket-var zero = top
bracket-var (suc i) = ignore-top (bracket-var i)

bracket-ƛ : Conv (Γ , α) β → Conv Γ (α `→ β)
bracket-ƛ (done t) = done (K · t)
bracket-ƛ top = done I
bracket-ƛ (use-top t) = t
bracket-ƛ (ignore-top t) = done K $$ t

bracket′ : Term Γ α → Conv Γ α
bracket′ tt = done tt
bracket′ (var i) = bracket-var i
bracket′ (ƛ t) = bracket-ƛ (bracket′ t)
bracket′ (t · s) = bracket′ t $$ bracket′ s

bracket : Term ∙ α → SKI α
bracket t with done s ← bracket′ t = s

--------------------------------------------------------------------------------

module _ where
  open ≡-Reasoning
  open import Tactic.Cong

  ⟦-⟧ᶜ-bracket-var : ∀ (i : Γ ∋ α) env
    → ⟦ bracket-var i ⟧ᶜ env ≡ lookupEnv env i
  ⟦-⟧ᶜ-bracket-var zero (env , x) = refl
  ⟦-⟧ᶜ-bracket-var (suc i) (env , x) = ⟦-⟧ᶜ-bracket-var i env

  ⟦-⟧ᶜ-$$-dist : ∀ (t : Conv Γ (α `→ β)) (s : Conv Γ α) env
    → ⟦ t $$ s ⟧ᶜ env ≡ ⟦ t ⟧ᶜ env (⟦ s ⟧ᶜ env)
  ⟦-⟧ᶜ-$$-dist (done t) (done s) env = refl
  ⟦-⟧ᶜ-$$-dist (done t) top (env , x) = refl
  ⟦-⟧ᶜ-$$-dist (done t) (use-top s) (env , x) =
    cong-app (⟦-⟧ᶜ-$$-dist (done (B · t)) s env) x
  ⟦-⟧ᶜ-$$-dist (done t) (ignore-top s) (env , x) =
    ⟦-⟧ᶜ-$$-dist (done t) s env
  ⟦-⟧ᶜ-$$-dist top (done t) (env , x) = refl
  ⟦-⟧ᶜ-$$-dist top (use-top s) (env , x) =
    cong-app (⟦-⟧ᶜ-$$-dist (done (S · I)) s env) x
  ⟦-⟧ᶜ-$$-dist top (ignore-top s) (env , x) =
    cong-app (⟦-⟧ᶜ-$$-dist (done (C · I)) s env) x
  ⟦-⟧ᶜ-$$-dist (use-top t) (done s) (env , x) =
    cong-app (⟦-⟧ᶜ-$$-dist (done (C · C · s)) t env) x
  ⟦-⟧ᶜ-$$-dist (use-top t) top (env , x) = begin
    ⟦ done S $$ t $$ done I ⟧ᶜ env x  ≡⟨ cong-app (⟦-⟧ᶜ-$$-dist (done S $$ t) (done I) env) x ⟩
    ⟦ done S $$ t ⟧ᶜ env id x         ≡⟨ cong-app₂ (⟦-⟧ᶜ-$$-dist (done S) t env) id x ⟩
    ⟦ t ⟧ᶜ env x x                    ∎
  ⟦-⟧ᶜ-$$-dist (use-top t) (use-top s) (env , x) = begin
    ⟦ done S $$ t $$ s ⟧ᶜ env x          ≡⟨ cong-app (⟦-⟧ᶜ-$$-dist (done S $$ t) s env) x ⟩
    ⟦ done S $$ t ⟧ᶜ env (⟦ s ⟧ᶜ env) x  ≡⟨ cong-app₂ (⟦-⟧ᶜ-$$-dist (done S) t env) _ x ⟩
    ⟦ t ⟧ᶜ env x (⟦ s ⟧ᶜ env x)          ∎
  ⟦-⟧ᶜ-$$-dist (use-top t) (ignore-top s) (env , x) = begin
    ⟦ done C $$ t $$ s ⟧ᶜ env x          ≡⟨ cong-app (⟦-⟧ᶜ-$$-dist (done C $$ t) s env) x ⟩
    ⟦ done C $$ t ⟧ᶜ env (⟦ s ⟧ᶜ env) x  ≡⟨ cong-app₂ (⟦-⟧ᶜ-$$-dist (done C) t env) _ x ⟩
    ⟦ t ⟧ᶜ env x (⟦ s ⟧ᶜ env)            ∎
  ⟦-⟧ᶜ-$$-dist (ignore-top t) (done s) (env , x) =
    ⟦-⟧ᶜ-$$-dist t (done s) env
  ⟦-⟧ᶜ-$$-dist (ignore-top t) top (env , x) = refl
  ⟦-⟧ᶜ-$$-dist (ignore-top t) (use-top s) (env , x) = begin
    ⟦ done B $$ t $$ s ⟧ᶜ env x          ≡⟨ cong-app (⟦-⟧ᶜ-$$-dist (done B $$ t) s env) x ⟩
    ⟦ done B $$ t ⟧ᶜ env (⟦ s ⟧ᶜ env) x  ≡⟨ cong-app₂ (⟦-⟧ᶜ-$$-dist (done B) t env) _ x ⟩
    ⟦ t ⟧ᶜ env (⟦ s ⟧ᶜ env x)            ∎
  ⟦-⟧ᶜ-$$-dist (ignore-top t) (ignore-top s) (env , x) =
    ⟦-⟧ᶜ-$$-dist t s env

  ⟦-⟧ᶜ-bracket-ƛ : ∀ (t : Conv (Γ , α) β) env x
    → ⟦ bracket-ƛ t ⟧ᶜ env x ≡ ⟦ t ⟧ᶜ (env , x)
  ⟦-⟧ᶜ-bracket-ƛ (done t) env x = refl
  ⟦-⟧ᶜ-bracket-ƛ top env x = refl
  ⟦-⟧ᶜ-bracket-ƛ (use-top t) env x = refl
  ⟦-⟧ᶜ-bracket-ƛ (ignore-top t) env x = cong-app (⟦-⟧ᶜ-$$-dist (done K) t env) x

  open import Axiom.Extensionality.Propositional using ( Extensionality )

  module _ (funExt : Extensionality _ _) where

    ⟦-⟧ᶜ-bracket′ : ∀ (t : Term Γ α) env → ⟦ bracket′ t ⟧ᶜ env ≡ ⟦ t ⟧′ env
    ⟦-⟧ᶜ-bracket′ tt env = refl
    ⟦-⟧ᶜ-bracket′ (var i) env = ⟦-⟧ᶜ-bracket-var i env
    ⟦-⟧ᶜ-bracket′ (ƛ t) env = funExt λ x → begin
      ⟦ bracket-ƛ (bracket′ t) ⟧ᶜ env x  ≡⟨ ⟦-⟧ᶜ-bracket-ƛ (bracket′ t) env x ⟩
      ⟦ bracket′ t ⟧ᶜ (env , x)          ≡⟨ ⟦-⟧ᶜ-bracket′ t (env , x) ⟩
      ⟦ t ⟧′ (env , x)                   ∎
    ⟦-⟧ᶜ-bracket′ (t · s) env = begin
      ⟦ bracket′ t $$ bracket′ s ⟧ᶜ env          ≡⟨ ⟦-⟧ᶜ-$$-dist (bracket′ t) (bracket′ s) env ⟩
      ⟦ bracket′ t ⟧ᶜ env (⟦ bracket′ s ⟧ᶜ env)  ≡⟨ cong! (⟦-⟧ᶜ-bracket′ s env) ⟩
      ⟦ bracket′ t ⟧ᶜ env (⟦ s ⟧′ env)           ≡⟨ cong-app (⟦-⟧ᶜ-bracket′ t env) _ ⟩
      ⟦ t ⟧′ env (⟦ s ⟧′ env)                    ∎

    ⟦-⟧ˢ-bracket : ∀ (t : Term ∙ α) → ⟦ bracket t ⟧ˢ ≡ ⟦ t ⟧
    ⟦-⟧ˢ-bracket t with bracket′ t | ⟦-⟧ᶜ-bracket′ t ∙
    ... | done s | eq = eq

--------------------------------------------------------------------------------

_ : bracket {α `→ α} (ƛ # 0) ≡ I
_ = refl

_ : bracket {α `→ β `→ α} (ƛ ƛ # 1) ≡ K
_ = refl

_ : bracket {(α `→ β `→ γ) `→ (α `→ β) `→ α `→ γ} (ƛ ƛ ƛ # 2 · # 0 · (# 1 · # 0)) ≡ S
_ = refl

_ : bracket {(β `→ γ) `→ (α `→ β) `→ α `→ γ} (ƛ ƛ ƛ # 2 · (# 1 · # 0)) ≡ B
_ = refl

_ : bracket {(α `→ β `→ γ) `→ β `→ α `→ γ} (ƛ ƛ ƛ # 2 · # 0 · # 1) ≡ C
_ = refl

church′ : ℕ → Term (∙ , α `→ α , α) α
church′ zero = # 0
church′ (suc n) = # 1 · (church′ n)

church : ℕ → Term ∙ ((α `→ α) `→ α `→ α)
church n = ƛ ƛ church′ n

_ : bracket {(α `→ α) `→ α `→ α} (church 0) ≡ K · I
_ = refl

_ : bracket {(α `→ α) `→ α `→ α} (church 1) ≡ I
_ = refl

_ : bracket {(α `→ α) `→ α `→ α} (church 2) ≡ S · B · I
_ = refl

_ : bracket {(α `→ α) `→ α `→ α} (church 3) ≡ S · B · (S · B · I)
_ = refl

_ : bracket {(α `→ α) `→ α `→ α} (church 4) ≡ S · B · (S · B · (S · B · I))
_ = refl
