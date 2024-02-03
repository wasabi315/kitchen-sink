{-# OPTIONS --cubical --guarded #-}

open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Cubical.Foundations.Everything
open import Cubical.Data.Bool using ( Bool; true; false; _and_; _or_; if_then_else_ )
open import Cubical.Data.List using ( List; []; _∷_ )

--------------------------------------------------------------------------------
-- Ref: https://github.com/agda/agda/blob/172366db528b28fb2eda03c5fc9804f2cdb1be18/test/Succeed/LaterPrims.agda

primitive
  primLockUniv : Type₁

LockU = primLockUniv

private
  variable
    ℓ : Level
    A B : Type ℓ

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {ℓ} → Type ℓ → Type ℓ
▹_ A = {{@tick α : Tick}} → A

▸_ : ∀ {ℓ} → ▹ Type ℓ → Type ℓ
▸ A = {{@tick α : Tick}} → A {{α}}

next : A → ▹ A
next x = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x = f x

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x = f x

transpLater : ∀ (A : I → ▹ Type) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 = transp (λ i → A i) i0 u0

transpLater-prim : (A : I → ▹ Type) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x {{α}} = transp (λ i → ▸ (A i {{α}})) i0 (x {{α}})

-- transpLater-test : ∀ (A : I → ▹ Type) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
-- transpLater-test A x = λ _ → transpLater-prim A x

hcompLater-prim : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 = hcomp (λ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = hcomp (λ { i (φ = i1) → u i 1=1 }) (outS u0)

-- hcompLater-test : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A))
--   → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
-- hcompLater-test A φ u x = λ _ → hcompLater-prim A φ u x

later-ext : ∀ {A : Type} {f g : ▹ A}
  → ▸ (f ≡ g)
  → (λ {{@tick a}} → f {{a}}) ≡ (λ {{@tick a}} → g {{a}})
later-ext eq i = eq i

postulate
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A) → (λ {{@tick α}} → dfix f {{α}}) ≡ f (λ {{@tick α}} → dfix f {{α}})

pfix' : (f : ▹ A → A) → ▸ (dfix f ≡ f λ {{α'}} → dfix f {{α'}})
pfix' f i = pfix f i

fix : (▹ A → A) → A
fix f = f (dfix f)

--------------------------------------------------------------------------------

data Stream (A : Type ℓ) : Type ℓ where
  _∷_ : A → ▹ Stream A → Stream A

-- even : Stream A → Stream A
-- even (x ∷ xs) = x ∷ even (tail xs)

--------------------------------------------------------------------------------

infixl 10 _+_
infixl 20 _·_
infixl 30 _*

record Lang (A : Type ℓ) : Type ℓ where
  inductive
  field
    ν : Bool
    δ : A → ▹ Lang A

open Lang

∅ : Lang A
∅ = fix λ ∅▹ → λ where
  .ν → false
  .δ _ → ∅▹

ε : Lang A
ν ε = true
δ ε _ = next ∅

⟦_⟧ : Bool → Lang Bool
ν ⟦ _ ⟧ = false
δ ⟦ false ⟧ false = next ε
δ ⟦ false ⟧ true = next ∅
δ ⟦ true ⟧ false = next ∅
δ ⟦ true ⟧ true = next ε

_+_ : Lang A → Lang A → Lang A
_+_ = fix λ _+▹_ a b → λ where
  .ν → ν a or ν b
  .δ x → δ a x +▹ δ b x

_·_ : Lang A → Lang A → Lang A
_·_ = fix λ _·▹_ a b → λ where
  .ν → ν a and ν b
  .δ x → if ν a
    then δ a x ·▹ b + δ b x
    else δ a x ·▹ b

_* : Lang A → Lang A
a * = fix λ a*▹ → λ where
  .ν → true
  .δ x → δ a x · a*▹
