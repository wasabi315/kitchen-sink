{-# OPTIONS --cubical --guarded #-}

module Guarded.Domain where

open import Cubical.Foundations.Everything
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using ( ℕ; zero; suc; _∸_ )

open import Guarded.Prims
open import Guarded.Partial

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    n : ℕ

--------------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data D : Type where
  fun : ▹ (D → D) → D
  later : ▹ D → D

_·_ : D → D → D
fun f▹ · d2 = later λ α → f▹ α d2
later d1▹ · d2 = later λ α → d1▹ α · d2

lam : (D → D) → D
lam f = fun (next f)

-- infixl 7 _·_ _·ᵈ_
-- infix 5 ƛ_ ƛᵈ-syntax

-- --------------------------------------------------------------------------------

-- data Exp : Type where
--   var : ℕ → Exp
--   _·_ : Exp → Exp → Exp
--   ƛ_ : Exp → Exp

-- --------------------------------------------------------------------------------

-- data Nf : Type
-- data Ne : Type

-- data Nf where
--   up : Ne → Nf
--   ƛ_ : Nf → Nf

-- data Ne where
--   var : ℕ → Ne
--   _·_ : Ne → Nf → Ne

-- --------------------------------------------------------------------------------

-- D-body : ▹ Type → Type
-- data D-body' (D▹ : ▹ Type) : Type
-- data Dⁿᵉ-body (D▹ : ▹ Type) : Type

-- D-body D▹ = Part (D-body' D▹)

-- data D-body' D▹ where
--   up : Dⁿᵉ-body D▹ → D-body' D▹
--   abs : ▸[ α ] (D▹ α → D▹ α) → D-body' D▹

-- data Dⁿᵉ-body D▹ where
--   var : ℕ → Dⁿᵉ-body D▹
--   _·_ : Dⁿᵉ-body D▹ → D-body D▹ → Dⁿᵉ-body D▹

-- D Dⁿᵉ : Type
-- D = fix D-body
-- Dⁿᵉ = Dⁿᵉ-body (next D)

-- D⇉ : D → D-body (next D)
-- D⇉ = transport $ fix-path D-body

-- ⇉D : D-body (next D) → D
-- ⇉D = transport⁻ $ fix-path D-body

-- δ : Part D → D
-- δ v = ⇉D (v >>= D⇉)

-- _·ᵈ'_ : D-body' (next D) → D → Part D
-- up e ·ᵈ' d = now (⇉D (now (up (e · D⇉ d))))
-- abs f▹ ·ᵈ' d = later λ α → now (f▹ α d)

-- _·ᵈ_ : D → D → D
-- d₁ ·ᵈ d₂ = δ do
--   f ← D⇉ d₁
--   f ·ᵈ' d₂

-- ƛᵈ-syntax : (D → D) → D
-- ƛᵈ-syntax = ⇉D ∘ now ∘ abs ∘ next
-- syntax ƛᵈ-syntax (λ u → v) = ƛᵈ u ⇒ v

-- Ω : D
-- Ω = (ƛᵈ x ⇒ x ·ᵈ x) ·ᵈ (ƛᵈ x ⇒ x ·ᵈ x)

-- --------------------------------------------------------------------------------

-- Env : Type
-- Env = ℕ → D

-- _▶_ : Env → D → Env
-- (ρ ▶ v) zero = v
-- (ρ ▶ v) (suc i) = ρ i

-- ⟦_⟧ : Exp → Env → D
-- ⟦ var i ⟧ ρ = ρ i
-- ⟦ e · d ⟧ ρ = ⟦ e ⟧ ρ ·ᵈ ⟦ d ⟧ ρ
-- ⟦ ƛ e ⟧ ρ = ƛᵈ d ⇒ ⟦ e ⟧ (ρ ▶ d)

-- {-# TERMINATING #-}
-- Rⁿᶠ : ℕ → D → Part Nf
-- Rⁿᶠ' : ℕ → D-body' (next D) → Part Nf
-- Rⁿᵉ : ℕ → Dⁿᵉ → Part Ne

-- Rⁿᶠ' n (up e) = do
--   e' ← Rⁿᵉ n e
--   return (up e')
-- Rⁿᶠ' n (abs f▹) = later λ α → do
--   f' ← Rⁿᶠ (suc n) (f▹ α (now (up (var n))))
--   return (ƛ f')

-- Rⁿᶠ n d = do
--   d' <- D⇉ d
--   Rⁿᶠ' n d'

-- Rⁿᵉ n (var k) = return (var (n ∸ suc k))
-- Rⁿᵉ n (e · d) = do
--   e' ← Rⁿᵉ n e
--   d' ← Rⁿᶠ n (⇉D d)
--   return (e' · d')

-- initEnv : ℕ → Env
-- initEnv n i = now (up (var (n ∸ suc i)))

-- nf : ℕ → Exp → Part Nf
-- nf n e = Rⁿᶠ n (⟦ e ⟧ (initEnv n))

-- -- --------------------------------------------------------------------------------

-- -- D-body : ▹ Type → Type
-- -- D-body D▹ = Partial (▸[ α ] (D▹ α → D▹ α))

-- -- D : Type
-- -- D = fix D-body

-- -- D⇉ : D → Partial (▹ (D → D))
-- -- D⇉ = transport $ fix-path D-body

-- -- ⇉D : Partial (▹ (D → D)) → D
-- -- ⇉D = transport⁻ $ fix-path D-body

-- -- δ : Partial D → D
-- -- δ v = ⇉D (v >>= D⇉)

-- -- _·ᵈ_ : D → (D → D)
-- -- u ·ᵈ v = δ do
-- --   f▹ ← D⇉ u
-- --   later λ α → now (f▹ α v)

-- -- ƛᵈ-syntax : (D → D) → D
-- -- ƛᵈ-syntax = ⇉D ∘ now ∘ next
-- -- syntax ƛᵈ-syntax (λ u → v) = ƛᵈ u ⇒ v

-- -- --------------------------------------------------------------------------------

-- -- ⇉D-D⇉ : ∀ v → ⇉D (D⇉ v) ≡ v
-- -- ⇉D-D⇉ = transport⁻Transport (fix-path D-body)

-- -- D⇉-⇉D : ∀ v → D⇉ (⇉D v) ≡ v
-- -- D⇉-⇉D = transportTransport⁻ (fix-path D-body)

-- -- ηᵈ : ∀ u → (ƛᵈ v ⇒ u ·ᵈ v) ≡ u
-- -- ηᵈ u =
-- --     (ƛᵈ v ⇒ u ·ᵈ v)
-- --   ≡⟨⟩
-- --     ⇉D (now λ _ v → u ·ᵈ v)
-- --   ≡⟨⟩
-- --     ⇉D (now λ _ v → ⇉D ((D⇉ u >>= λ f▹ → later λ α → now (f▹ α v)) >>= D⇉))
-- --   ≡⟨ {!   !} ⟩
-- --     u
-- --   ∎

-- -- _ : ∀ (f : D → D) u → (ƛᵈ v ⇒ f v) ·ᵈ u ≡ f u
-- -- _ = {!   !}

-- -- --------------------------------------------------------------------------------

-- -- Env : ℕ → Type
-- -- Env n = Fin n → D

-- -- _▶_ : Env n → D → Env (suc n)
-- -- (ρ ▶ v) (zero , _) = v
-- -- (ρ ▶ v) (suc i , p) = ρ (i , pred-≤-pred p)

-- -- eval : (ρ : Env n) → Exp n → D
-- -- eval ρ (var i) = ρ i
-- -- eval ρ (t · u) = eval ρ t ·ᵈ eval ρ u
-- -- eval ρ (ƛ t) = ƛᵈ v ⇒ eval (ρ ▶ v) t

-- -- evaluate : Exp 0 → D
-- -- evaluate = eval (⊥.rec ∘ ¬Fin0)

-- -- 𝕀 : Exp 0
-- -- 𝕀 = ƛ var fzero

-- -- 𝕂 : Exp 0
-- -- 𝕂 = ƛ ƛ var (fsuc fzero)
