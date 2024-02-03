{-# OPTIONS --cubical --guarded #-}

open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Data.Empty using () renaming ( ⊥* to Empty*; rec to exFalso )
open import Cubical.Data.Unit using ( Unit*; tt )

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

later-ext : ∀ {A : Set} → {f g : ▹ A} → (▸ λ α → f α ≡ g α) → f ≡ g
later-ext eq = λ i α → eq α i

postulate
  dfix : ∀ {ℓ} {A : Type ℓ} → (▹ A → A) → ▹ A
  pfix : ∀ {ℓ} {A : Type ℓ} (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

pfix' : ∀ {ℓ} {A : Type ℓ} (f : ▹ A → A) → ▸ λ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : ∀ {ℓ} {A : Type ℓ} → (▹ A → A) → A
fix f = f (dfix f)

--------------------------------------------------------------------------------

infixr 5 _∷_ _∷▹_

-- data PartialColist (A : Type ℓ) : Type ℓ where
--   [] : PartialColist A
--   ⊥ : PartialColist A
--   _∷_ : (x : A) (xs : ▹ PartialColist A) → PartialColist A
--   ⊥-⊥ : ∀ x → x ∷ next ⊥ ≡ ⊥
--   trunc : isSet (PartialColist A)

-- _∷▹_ : A → PartialColist A → PartialColist A
-- x ∷▹ xs = x ∷ next xs

-- map : (A → B) → PartialColist A → PartialColist B
-- map f [] = []
-- map f ⊥ = ⊥
-- map f (x ∷ xs) = f x ∷ λ α → map f (xs α)
-- map f (⊥-⊥ x i) = ⊥-⊥ (f x) i
-- map f (trunc xs ys p q i j) = trunc _ _ (cong (map f) p) (cong (map f) q) i j

-- _ : tt ∷▹ tt ∷▹ tt ∷▹ ⊥ ≡ ⊥
-- _ = cong (tt ∷▹_) (cong (tt ∷▹_) (⊥-⊥ tt) ∙  ⊥-⊥ tt) ∙ ⊥-⊥ tt

-- The Colist datatype is a possibly infinite list of elements of type A, defined using the tick modality.
data Colist (A : Type) : Type where
  [] : Colist A
  _∷_ : (x : A) (xs : ▹ Colist A) → Colist A

-- singleton returns a colist with one element.
singleton : A → Colist A
singleton x = x ∷ next []

-- map applies a function to each element of a colist.
map : (A → B) → Colist A → Colist B
map f [] = []
map f (x ∷ xs) = f x ∷ λ α → map f (xs α)

-- Finite is a predicate on colists that is inhabited if the colist is finite.
data Finite {A} : Colist A → Set where
  [] : Finite []
  _∷_ : ∀ x {xs} → Finite xs → Finite (x ∷ next xs)

-- singleton x is finite.
singleton-finite : (x : A) → Finite (singleton x)
singleton-finite x = x ∷ []

-- map preserves finiteness.
map-finite : ∀ {A B} (f : A → B) {xs} → Finite xs → Finite (map f xs)
map-finite f [] = []
map-finite f (x ∷ xs) = f x ∷ map-finite f xs
