{-# OPTIONS --cubical --guarded #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Function

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
-- Colists and operations on them

infixr 5 _∷_

data Colist (A : Type) : Type where
  [] : Colist A
  _∷_ : (x : A) (xs : ▹ Colist A) → Colist A

map : (A → B) → Colist A → Colist B
map f [] = []
map f (x ∷ xs) = f x ∷ λ α → map f (xs α)

foldr : (A → ▹ B → B) → B → Colist A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x λ α → foldr f z (xs α)

scanl : (A → B → A) → A → Colist B → Colist A
scanl f z [] = z ∷ next []
scanl f z (x ∷ xs) = z ∷ λ α → scanl f (f z x) (xs α)

ColistC : Type → Type₁
ColistC A = ∀ (B : Type) (cons : A → ▹ B → B) (nil : B) → B

build : ColistC A → Colist A
build f = f _ _∷_ []

--------------------------------------------------------------------------------
-- Rewrite rules

mapFB : (A → ▹ C → C) → (B → A) → (B → ▹ C → C)
mapFB c f = λ x ys → c (f x) ys

rule-map : ∀ (f : A → B) xs
  → map f xs ≡ build (λ _ c n → foldr (mapFB c f) n xs)
rule-map f [] = refl
rule-map f (x ∷ xs) = congS (f x ∷_) (later-ext λ α → rule-map f (xs α))

rule-mapList : ∀ (f : A → B) → foldr (mapFB _∷_ f) [] ≡ map f
rule-mapList f i [] = []
rule-mapList f i (x ∷ xs) = f x ∷ λ α → rule-mapList f i (xs α)

rule-mapFB : ∀ (c : A → ▹ D → D) (f : B → A) (g : C → B)
  → mapFB (mapFB c f) g ≡ mapFB c (f ∘ g)
rule-mapFB c f g = refl

rule-mapFB/id : ∀ (c : A → ▹ B → B) → mapFB c (λ x → x) ≡ c
rule-mapFB/id c = refl

scanlFB : (B → A → B) → (B → ▹ C → C) → (A → ▹ (B → C) → (B → C))
scanlFB f c = λ b g x → let b' = f x b in c b' λ α → g α b'

rule-scanl : ∀ (f : B → A → B) z xs
  → scanl f z xs ≡ build (λ _ c n → c z (next (foldr (scanlFB f c) (const n) xs z)))
rule-scanl f z [] = refl
rule-scanl f z (x ∷ xs) = congS (z ∷_) (later-ext λ α → {! rule-scanl f (f z x) (xs α) !})

--------------------------------------------------------------------------------
-- Parametricity-exploiting proof
-- Ref: https://wiki.portal.chalmers.se/agda/Libraries/LightweightFreeTheorems

infixr 0 _[→]_

[Type_] : ∀ ℓ → Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
[Type ℓ ] A₁ A₂ = A₁ → A₂ → Type ℓ
[Type₁] = [Type (ℓ-suc ℓ-zero) ]
[Type] = [Type ℓ-zero ]

Π : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Π A B = (a : A) → B a

[Π] : ∀ {A₁ A₂ B₁ B₂} →
  ([A] : [Type ℓ ] A₁ A₂) →
  ([B] : ∀ {a₁ a₂} → [A] a₁ a₂ → [Type ℓ' ] (B₁ a₁) (B₂ a₂)) →
  [Type (ℓ-max ℓ ℓ') ] (Π A₁ B₁) (Π A₂ B₂)
[Π] [A] [B] f₁ f₂ = ∀ {a₁ a₂} [a] → [B] [a] (f₁ a₁) (f₂ a₂)

_[→]_ : ∀ {A₁ A₂ B₁ B₂} →
  [Type ℓ ] A₁ A₂ →
  [Type ℓ' ] B₁ B₂ →
  [Type (ℓ-max ℓ ℓ') ] (A₁ → B₁) (A₂ → B₂)
[A] [→] [B] = [Π] [A] λ _ → [B]

-- I'm not sure if this is the right way to define the relation for ▸_
[▸]_ : ∀ {A₁ A₂} → ([A]▹ : ▸ λ α → [Type ℓ ] (A₁ α) (A₂ α)) → [Type ℓ ] (▸ A₁) (▸ A₂)
([▸] [A]▹) x₁ x₂ = ▸ λ α → [A]▹ α (x₁ α) (x₂ α)

[▹]_ : ∀ {A₁ A₂} → ([A] : [Type ℓ ] A₁ A₂) → [Type ℓ ] (▹ A₁) (▹ A₂)
[▹] [A] = [▸] λ _ → [A]

data [Colist] {A₁ A₂} ([A] : [Type] A₁ A₂) : [Type] (Colist A₁) (Colist A₂) where
  [[]] : [Colist] [A] [] []
  [∷] : ([A] [→] [▹] [Colist] [A] [→] [Colist] [A]) _∷_ _∷_

[ColistC] : ∀ {A₁ A₂} ([A] : [Type] A₁ A₂) → [Type₁] (ColistC A₁) (ColistC A₂)
[ColistC] [A] = [Π] [Type] λ [B] → ([A] [→] [▹] [B] [→] [B]) [→] [B] [→] [B]
