{-# OPTIONS --cubical --guarded #-}

open import Cubical.Foundations.Everything

--------------------------------------------------------------------------------
-- Ref: https://github.com/agda/agda/blob/172366db528b28fb2eda03c5fc9804f2cdb1be18/test/Succeed/LaterPrims.agda

primitive
  primLockUniv : Type₁

LockU = primLockUniv

private
  variable
    ℓ ℓ' : Level
    A B C D : Type ℓ

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : Type ℓ → Type ℓ
▹_ A = (@tick @irr α : Tick) -> A -- Note @irr!

▸_ : ▹ Type ℓ → Type ℓ
▸ A = (@tick @irr α : Tick) → A α

▸-syntax : ▹ Type ℓ → Type ℓ
▸-syntax = ▸_

infix 2 ▸-syntax
syntax ▸-syntax (λ α → A) = ▸[ α ] A

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x α = f α (x α)

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

pfix' : (f : ▹ A → A) → ▸[ α ] dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ≡ f (next (fix f))
fix-path f i = f (pfix f i)

--------------------------------------------------------------------------------

-- Now tick-irr holds definitionally
tick-irr : (x : ▹ A) → ▸[ α ] ▸[ β ] x α ≡ x β
tick-irr x _ _ = refl

--------------------------------------------------------------------------------

data Stream (A : Type ℓ) : Type ℓ where
  _∷_ : (x : A) (xs : ▹ Stream A) → Stream A

∷-syntax : A → ▹ Stream A → Stream A
∷-syntax = _∷_

infixr 5 ∷-syntax
syntax ∷-syntax x (λ α → xs) = x ∷[ α ] xs

dup1 dup2 : Stream A → Stream A
dup1 (x ∷ xs) = x ∷[ α ] x ∷[ β ] dup1 (xs α)
dup2 (x ∷ xs) = x ∷[ α ] x ∷[ β ] dup2 (xs β)

lem1 lem2 : dup1 {A = A} ≡ dup2
lem1 i (x ∷ xs) = x ∷[ α ] x ∷[ β ] lem1 i (xs α)
lem2 i (x ∷ xs) = x ∷[ α ] x ∷[ β ] lem2 i (xs β)

lem3 lem4 : lem1 {A = A} ≡ lem2
lem3 i j (x ∷ xs) = x ∷[ α ] x ∷[ β ] lem3 i j (xs α)
lem4 i j (x ∷ xs) = x ∷[ α ] x ∷[ β ] lem4 i j (xs β)

lem5 lem6 : lem3 {A = A} ≡ lem4
lem5 i j k (x ∷ xs) = x ∷[ α ] x ∷[ β ] lem5 i j k (xs α)
lem6 i j k (x ∷ xs) = x ∷[ α ] x ∷[ β ] lem6 i j k (xs β)
