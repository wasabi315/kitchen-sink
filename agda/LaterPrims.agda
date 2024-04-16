{-# OPTIONS --cubical --guarded #-}

module LaterPrims where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base using ( zero; suc )

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

transpLater : ∀ (A : I → ▹ Type ℓ) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 α = transp (λ i → A i α) i0 (u0 α)

transpLater-prim : (A : I → ▹ Type ℓ) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = transp (λ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Type ℓ) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x _ = transpLater-prim A x

hcompLater-prim : ∀ (A : ▹ Type ℓ) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 α = hcomp (λ { i (φ = i1) → u i 1=1 α }) (outS u0 α)

hcompLater : ∀ (A : ▹ Type ℓ) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = hcomp (λ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Type ℓ) φ (u : I → Partial φ (▸ A))
  → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x _ = hcompLater-prim A φ u x

later-ext : {f g : ▹ A} → ▸[ α ] f α ≡ g α → f ≡ g
later-ext eq i α = eq α i

later-ext⁻ : {f g : ▹ A} → f ≡ g → ▸[ α ] f α ≡ g α
later-ext⁻ eq α i = eq i α

later-extP : {A B : ▹ Type ℓ} {P : A ≡ B} {f : ▸[ α ] P i0 α} {g : ▸[ α ] P i1 α}
  → ▸[ α ] PathP (λ i → P i α) (f α) (g α)
  → PathP (λ i → ▸[ α ] P i α) f g
later-extP eq i α = eq α i

later-extP⁻ : {A B : ▹ Type ℓ} {P : A ≡ B} {f : ▸[ α ] P i0 α} {g : ▸[ α ] P i1 α}
  → PathP (λ i → ▸[ α ] P i α) f g
  → ▸[ α ] PathP (λ i → P i α) (f α) (g α)
later-extP⁻ eq α i = eq i α

postulate
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

pfix' : (f : ▹ A → A) → ▸ λ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ≡ f (next (fix f))
fix-path f i = f (pfix f i)

isContr▹ : {A : ▹ Type ℓ}
  → ▸[ α ] isContr (A α)
  → isContr (▸[ α ] A α)
fst (isContr▹ p) α = fst (p α)
snd (isContr▹ p) x i α = snd (p α) (x α) i

isProp▹ : {A : ▹ Type ℓ}
  → ▸[ α ] (isProp (A α))
  → isProp (▸[ α ] A α)
isProp▹ p x y i α = p α (x α) (y α) i

isOfHLevel▹ : (n : HLevel) {A : ▹ Type ℓ}
  → ▸[ α ] (isOfHLevel n (A α))
  → isOfHLevel n (▸[ α ] A α)
isOfHLevel▹ 0 = isContr▹
isOfHLevel▹ 1 = isProp▹
isOfHLevel▹ (suc (suc n)) p x y =
  isOfHLevelRetract (suc n)
    (λ eq α i → eq i α)
    (λ eq▹ i α → eq▹ α i)
    (λ _ → refl)
    (isOfHLevel▹ (suc n) λ α → p α (x α) (y α))
