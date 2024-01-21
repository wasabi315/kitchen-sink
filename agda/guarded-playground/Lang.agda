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
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {ℓ} → ▹ Type ℓ → Type ℓ
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

transpLater : ∀ (A : I → ▹ Type) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = transp (λ i → A i a) i0 (u0 a)

transpLater-prim : (A : I → ▹ Type) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = transp (λ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Type) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x = λ _ → transpLater-prim A x

hcompLater-prim : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 a = hcomp (λ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

hcompLater : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = hcomp (λ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Type) φ (u : I → Partial φ (▸ A))
  → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x = λ _ → hcompLater-prim A φ u x

later-ext : ∀ {A : Set} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

postulate
  dfix : ∀ {ℓ} {A : Type ℓ} → (▹ A → A) → ▹ A
  pfix : ∀ {ℓ} {A : Type ℓ} (f : ▹ A → A) → dfix f ≡ (\ _ → f (dfix f))

pfix' : ∀ {ℓ} {A : Type ℓ} (f : ▹ A → A) → ▸ \ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : ∀ {ℓ} {A : Type ℓ} → (▹ A → A) → A
fix f = f (dfix f)

--------------------------------------------------------------------------------
-- The delay monad

data Delay (A : Type) : Type where
  now : A → Delay A
  later : ▹ Delay A → Delay A
  later-later : ∀ x → x ≡ later (next x)

⊥ : ∀ {A} → Delay A
⊥ = fix λ ⊥▹ → later ⊥▹

--------------------------------------------------------------------------------
-- The finite language example but in Guarded Agda
-- Ref: https://agda.readthedocs.io/en/latest/language/sized-types.html

infixl 10 _+_
infixl 20 _·_
infixl 30 _*

record Lang (A : Type) : Type where
  inductive
  field
    ν : Bool
    δ : A → ▹ Lang A

open Lang

∅ : ∀ {A} → Lang A
∅ = fix λ ∅▹ → λ where
  .ν → false
  .δ _ → ∅▹

ε : ∀ {A} → Lang A
ν ε = true
δ ε _ = next ∅

⟦_⟧ : Bool → Lang Bool
ν ⟦ _ ⟧ = false
δ ⟦ false ⟧ false = next ε
δ ⟦ false ⟧ true = next ∅
δ ⟦ true ⟧ false = next ∅
δ ⟦ true ⟧ true = next ε

_+_ : ∀ {A} → Lang A → Lang A → Lang A
_+_ = fix λ where
  +▹ a b .ν → ν a or ν b
  +▹ a b .δ x α → +▹ α (δ a x α) (δ b x α)

_·_ : ∀ {A} → Lang A → Lang A → Lang A
_·_ = fix λ where
  ·▹ a b .ν → ν a and ν b
  ·▹ a b .δ x α → if ν a
    then ·▹ α (δ a x α) b + δ b x α
    else ·▹ α (δ a x α) b

_* : ∀ {A} → Lang A → Lang A
_* = fix λ where
  *▹ a .ν → true
  *▹ a .δ x α → δ a x α · *▹ α a

-- I want Bool here instead but don't know how
_∈_ : ∀ {A} → List A → Lang A → Delay Bool
[] ∈ a = now (ν a)
(x ∷ xs) ∈ a = later λ α → xs ∈ δ a x α

bip-bop = (⟦ true ⟧ · ⟦ false ⟧) *

test₁ : (true ∷ false ∷ []) ∈ bip-bop ≡ now true
test₁ =
  sym (
    later-later (now true) ∙
    cong later (later-ext λ α →
      later-later (now true) ∙
      cong later (later-ext λ α' →
        cong now {!   !})))
