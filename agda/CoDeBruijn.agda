module CoDeBruijn where

open import Data.Bool hiding (T)
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

private
  variable
    i j m n o : ℕ

infix  4 _⊑_ _⇑_ _↑_ _‼_
infixr 5 _⨟_ _∷⟨_↑_⟩
infixr 6 ƛ_
infixl 8 _·_ _·ᶜ_ _·ᵛ_
infixr 9 T_ K_ L_ R_ B_

--------------------------------------------------------------------------------
-- Thinning and covering

data _⊑_ : ℕ → ℕ → Set where
  ∙  : 0 ⊑ 0
  T_ : m ⊑ n → m ⊑ suc n -- thin
  K_ : m ⊑ n → suc m ⊑ suc n -- keep

data Cover : ℕ → ℕ → ℕ → Set where
  ∙  : Cover 0 0 0
  L_ : Cover m n o → Cover (suc m) n (suc o) -- left
  R_ : Cover m n o → Cover m (suc n) (suc o) -- right
  B_ : Cover m n o → Cover (suc m) (suc n) (suc o) -- both

-- Thinned thing
record _⇑_ (S : ℕ → Set) (m : ℕ) : Set where
  constructor _↑_
  field
    {support} : ℕ
    thing     : S support
    thinnning : support ⊑ m

open _⇑_ public

∙⊑ : 0 ⊑ m
∙⊑ {zero}  = ∙
∙⊑ {suc m} = T ∙⊑

id⊑ : ∀ {m} → m ⊑ m
id⊑ {zero}  = ∙
id⊑ {suc m} = K id⊑

_⨟_ : m ⊑ n → n ⊑ o → m ⊑ o
θ   ⨟ ∙   = θ
θ   ⨟ T φ = T (θ ⨟ φ)
T θ ⨟ K φ = T (θ ⨟ φ)
K θ ⨟ K φ = K (θ ⨟ φ)

thin⇑ : {S : ℕ → Set} → m ⊑ n → S ⇑ m → S ⇑ n
thin⇑ θ (x ↑ φ) = x ↑ φ ⨟ θ

thinL : Cover m n o → m ⊑ o
thinL ∙     = ∙
thinL (L c) = K thinL c
thinL (R c) = T thinL c
thinL (B c) = K thinL c

thinR : Cover m n o → n ⊑ o
thinR ∙     = ∙
thinR (L c) = T thinR c
thinR (R c) = K thinR c
thinR (B c) = K thinR c

coprod : i ⊑ m → j ⊑ m → ∃[ n ] Cover i j n × n ⊑ m
coprod ∙        ∙  = 0 , ∙ , ∙
coprod (T θ) (T φ) = let _ , c , ψ = coprod θ φ in -,   c , T ψ
coprod (T θ) (K φ) = let _ , c , ψ = coprod θ φ in -, R c , K ψ
coprod (K θ) (T φ) = let _ , c , ψ = coprod θ φ in -, L c , K ψ
coprod (K θ) (K φ) = let _ , c , ψ = coprod θ φ in -, B c , K ψ

--------------------------------------------------------------------------------
-- Lambda terms with co-de Bruijn indices

sucIf : Bool → ℕ → ℕ
sucIf b n = if b then suc n else n

data Term′ : ℕ → Set where
  var : Term′ 1
  lam : (use : Bool) → Term′ (sucIf use n) → Term′ n
  app : Cover m n o → Term′ m → Term′ n → Term′ o

Term = Term′ ⇑_

var′ : 1 ⊑ n → Term n
var′ i = var ↑ i

ƛ_ : Term (suc n) → Term n
ƛ_ (t ↑ T θ) = lam false t ↑ θ
ƛ_ (t ↑ K θ) = lam true  t ↑ θ

_·_ : Term n → Term n → Term n
(t ↑ θ) · (u ↑ φ) = let _ , c , ψ = coprod θ φ in app c t u ↑ ψ

--------------------------------------------------------------------------------
-- Values

mutual

  data Val′ : ℕ → Set where
    lam   : Closure m → Val′ m
    rigid : Spine m → Val′ m

  data Closure : ℕ → Set where
    clos : m ⊑ n → Env o n → (use : Bool) → Term′ (sucIf use m) → Closure o

  data Spine : ℕ → Set where
    ∙   : Spine 1
    app : Cover m n o → Spine m → Val′ n → Spine o

  data Env : ℕ → ℕ → Set where
    ∙       : Env m 0
    _∷⟨_↑_⟩ : Val m → Env n o → n ⊑ m → Env m (suc o)

  Val = Val′ ⇑_

thinEnv : m ⊑ n → Env m o → Env n o
thinEnv _ ∙              = ∙
thinEnv θ (t ∷⟨ ρ ↑ φ ⟩) = thin⇑ θ t ∷⟨ ρ ↑ φ ⨟ θ ⟩

_‼_ : Env m n → 1 ⊑ n → Val m
_ ∷⟨ ρ ↑ φ ⟩ ‼ T θ = thin⇑ φ (ρ ‼ θ)
t ∷⟨ _ ↑ _ ⟩ ‼ K θ = t

--------------------------------------------------------------------------------
-- Evaluation and read-back

{-# TERMINATING #-}
mutual

  eval : Env m n → Term n → Val m
  eval ρ (var       ↑ θ) = ρ ‼ θ
  eval ρ (lam φ t   ↑ θ) = lam (clos θ ρ φ t) ↑ id⊑
  eval ρ (app c t u ↑ θ) = eval ρ (t ↑ thinL c ⨟ θ) ·ᵛ eval ρ (u ↑ thinR c ⨟ θ)

  _·ᶜ_ : Closure ⇑ m → Val m → Val m
  (clos θ ρ false t ↑ φ) ·ᶜ m = eval (thinEnv φ ρ) (t ↑ θ)
  (clos θ ρ true  t ↑ φ) ·ᶜ m = eval (m ∷⟨ ρ ↑ φ ⟩) (t ↑ K θ)

  _·ᵛ_ : Val m → Val m → Val m
  (rigid sp ↑ θ) ·ᵛ (u ↑ φ) = let _ , c , ψ = coprod θ φ in rigid (app c sp u) ↑ ψ
  (lam cl   ↑ θ) ·ᵛ u       = (cl ↑ θ) ·ᶜ u

{-# TERMINATING #-}
mutual

  readBack : Val m → Term m
  readBack (lam cl   ↑ θ) = ƛ readBack ((cl ↑ T θ) ·ᶜ (rigid ∙ ↑ K ∙⊑))
  readBack (rigid sp ↑ θ) = readBackSpine (sp ↑ θ)

  readBackSpine : Spine ⇑ m → Term m
  readBackSpine (∙          ↑ θ) = var ↑ (K ∙⊑ ⨟ θ)
  readBackSpine (app c sp t ↑ θ) = thin⇑ θ (readBackSpine (sp ↑ thinL c) · readBack (t ↑ thinR c))

nf : Env m n → Term n → Term m
nf ρ t = readBack (eval ρ t)

--------------------------------------------------------------------------------

𝕀 : Term 0
𝕀 = ƛ var′ (K ∙)

𝕂 : Term 0
𝕂 = ƛ ƛ var′ (T K ∙)

𝕊 : Term 0
𝕊 = ƛ ƛ ƛ var′ (T T K ∙) · var′ (K T T ∙) · (var′ (T K T ∙) · var′ (K T T ∙))

Ch′ : ℕ → Term 2
Ch′ zero    = var′ (K T ∙)
Ch′ (suc n) = var′ (T K ∙) · Ch′ n

Ch : ℕ → Term 0
Ch n = ƛ ƛ Ch′ n

add : Term 0
add = ƛ ƛ ƛ ƛ var′ (T T T K ∙) · var′ (T K T T ∙) · (var′ (T T K T ∙) · var′ (T K T T ∙) · var′ (K T T T ∙))

_ : 𝕂 ≡ (lam true (lam false var) ↑ ∙)
_ = refl

_ : nf ∙ (𝕊 · 𝕂 · 𝕊 · 𝕂) ≡ 𝕂
_ = refl

_ : nf ∙ (add · Ch 2 · Ch 40) ≡ Ch 42
_ = refl
