{-# OPTIONS --cubical --guarded #-}

module LaterPrims where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

--------------------------------------------------------------------------------
-- Ref: https://github.com/agda/agda/blob/172366db528b28fb2eda03c5fc9804f2cdb1be18/test/Succeed/LaterPrims.agda

primitive
  primLockUniv : Type₁

LockU = primLockUniv

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : Type ℓ → Type ℓ
▹_ A = (@tick α : Tick) -> A
infix 2 ▹_

▸_ : ▹ Type ℓ → Type ℓ
▸ A = (@tick α : Tick) → A α
infix 2 ▸_

▸-syntax = ▸_
syntax ▸-syntax (λ α → A) = ▸[ α ] A
infix 2 ▸-syntax

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x α = f α (x α)
infixl 4 _⊛_

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

transpLater : ∀ (A : I → ▹ Type) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 α = transp (λ i → A i α) i0 (u0 α)

transpLater-prim : (A : I → ▹ Type) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = transp (λ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Type) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x _ = transpLater-prim A x

hcompLater-prim : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 α = hcomp (λ { i (φ = i1) → u i 1=1 α }) (outS u0 α)

hcompLater : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = hcomp (λ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A))
  → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x _ = hcompLater-prim A φ u x

later-ext : {f g : ▹ A} → (▸ λ α → f α ≡ g α) → f ≡ g
later-ext eq i α = eq α i

postulate
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

pfix' : (f : ▹ A → A) → ▸ λ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ≡ f (next (fix f))
fix-path f i = f (pfix f i)
