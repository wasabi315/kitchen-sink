{-# OPTIONS --cubical --guarded #-}

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool using ( Bool; true; false; if_then_else_; _and_ )

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
▹_ A = (@tick α : Tick) -> A

▸_ : ▹ Type ℓ → Type ℓ
▸ A = (@tick α : Tick) → A α

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

pfix' : (f : ▹ A → A) → ▸ λ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

--------------------------------------------------------------------------------

infixr 5 _∷_ _∷▹_

data PartialColist (A : Type ℓ) : Type ℓ where
  [] : PartialColist A
  _∷_ : (x : A) (xs : ▹ PartialColist A) → PartialColist A
  τ : (xs : ▹ PartialColist A) → PartialColist A
  τ⁻ : ∀ xs → τ (next xs) ≡ xs
  trunc : isSet (PartialColist A)

_∷▹_ : A → PartialColist A → PartialColist A
x ∷▹ xs = x ∷ next xs

⊥ : PartialColist A
⊥ = fix τ

map : (A → B) → PartialColist A → PartialColist B
map f [] = []
map f (x ∷ xs) = f x ∷ λ α → map f (xs α)
map f (τ xs) = τ λ α → map f (xs α)
map f (τ⁻ xs i) = τ⁻ (map f xs) i
map f (trunc xs ys p q i j) = trunc _ _ (cong (map f) p) (cong (map f) q) i j

filter : (A → Bool) → PartialColist A → PartialColist A
filter f [] = []
filter f (x ∷ xs) = (if f x then (x ∷_) else τ) λ α → filter f (xs α)
filter f (τ xs) = τ λ α → filter f (xs α)
filter f (τ⁻ xs i) = τ⁻ (filter f xs) i
filter f (trunc xs ys p q i j) = trunc _ _ (cong (filter f) p) (cong (filter f) q) i j

--------------------------------------------------------------------------------
-- Properties

bip-bop = fix λ bip-bop▹ → true ∷▹ false ∷ bip-bop▹

lem-bip-bop : filter (idfun Bool) bip-bop ≡ true ∷ next (filter (idfun Bool) bip-bop)
lem-bip-bop = congS (true ∷_) (later-ext λ α → {!   !})

filter-filter : ∀ (f g : A → Bool) xs
  → filter f (filter g xs) ≡ filter (λ x → g x and f x) xs
filter-filter f g [] = refl
filter-filter f g (x ∷ xs) with g x
... | false = cong τ (later-ext λ α → filter-filter f g (xs α))
... | true = cong (if f x then x ∷_ else τ) (later-ext λ α → filter-filter f g (xs α))
filter-filter f g (τ xs) = cong τ (later-ext λ α → filter-filter f g (xs α))
filter-filter f g (τ⁻ xs i) = isSet→isSet' trunc
  (cong τ (later-ext λ α → filter-filter f g xs))
  (filter-filter f g xs)
  (λ j → filter f (filter g (τ⁻ xs j)))
  (λ j → filter (λ x → g x and f x) (τ⁻ xs j))
  i
filter-filter f g (trunc xs ys p q i j) = isGroupoid→isGroupoid' (isSet→isGroupoid trunc)
  (λ k → filter-filter f g (p k))
  (λ k → filter-filter f g (q k))
  (λ k → filter-filter f g xs)
  (λ k → filter-filter f g ys)
  (λ k l → filter f (filter g (trunc xs ys p q k l)))
  (λ k l → filter (λ x → g x and f x) (trunc xs ys p q k l))
  i j
