{-# OPTIONS --rewriting #-}

module Regular where

open import Level using (Lift; lift)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base as Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (_↔_; mk↔; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂)

private
  variable
    A B C : Set
    m n o p : ℕ

infixl 5  _▷_ _⨟_
infix  5  `μ_
infixr 6  _`+_
infixr 7  _`×_
infix  8  _↑
infixl 9  _[_] _[_]₀
infixr 10 ∂[_]_

--------------------------------------------------------------------------------

-- Descriptions of regular types with explicit weakening representation
data Reg : ℕ → Set where
  ∙    : Reg (suc n)
  _↑   : Reg n → Reg (suc n)
  `0   : Reg n
  _`+_ : (α β : Reg n) → Reg n
  `1   : Reg n
  _`×_ : (α β : Reg n) → Reg n
  `μ_  : (α : Reg (suc n)) → Reg n

data Sub : (m n : ℕ) → Set where
  id  : Sub n n
  _↑  : (σ : Sub m n) → Sub (suc m) n
  _▷_ : (σ : Sub m n) (α : Reg m) → Sub m (suc n)

private
  variable
    α β γ : Reg n
    σ τ ν : Sub m n

_[_] : Reg m → Sub n m → Reg n
α        [ id ]        = α
α        [ σ ↑ ]       = α [ σ ] ↑
∙        [ σ ▷ γ ]     = γ
(α ↑)    [ σ ▷ γ ]     = α [ σ ]
`0       [ σ@(_ ▷ _) ] = `0
(α `+ β) [ σ@(_ ▷ _) ] = α [ σ ] `+ β [ σ ]
`1       [ σ@(_ ▷ _) ] = `1
(α `× β) [ σ@(_ ▷ _) ] = α [ σ ] `× β [ σ ]
(`μ α)   [ σ@(_ ▷ _) ] = `μ α [ σ ↑ ▷ ∙ ]

_[_]₀ : Reg (suc n) → Reg n → Reg n
α [ β ]₀ = α [ id ▷ β ]

_⨟_ : Sub n o → Sub m n → Sub m o
σ       ⨟ id        = σ
σ       ⨟ τ ↑       = (σ ⨟ τ) ↑
id      ⨟ τ@(_ ▷ _) = τ
(σ ↑)   ⨟ (τ ▷ _)   = σ ⨟ τ
(σ ▷ α) ⨟ τ@(_ ▷ _) = (σ ⨟ τ) ▷ (α [ τ ])

[][] : (α : Reg o) (σ : Sub n o) (τ : Sub m n) → α [ σ ] [ τ ] ≡ α [ σ ⨟ τ ]
[][] α        σ         id = refl
[][] α        σ         (τ ↑) = cong _↑ ([][] α σ τ)
[][] α        id        τ@(_ ▷ _) = refl
[][] α        (σ ↑)     (τ ▷ β) = [][] α σ τ
[][] ∙        (σ ▷ α)   τ@(_ ▷ _) = refl
[][] (α ↑)    (σ ▷ β)   τ@(_ ▷ _) = [][] α σ τ
[][] `0       σ@(_ ▷ _) τ@(_ ▷ _) = refl
[][] (α `+ β) σ@(_ ▷ _) τ@(_ ▷ _) = cong₂ _`+_ ([][] α σ τ) ([][] β σ τ)
[][] `1       σ@(_ ▷ _) τ@(_ ▷ _) = refl
[][] (α `× β) σ@(_ ▷ _) τ@(_ ▷ _) = cong₂ _`×_ ([][] α σ τ) ([][] β σ τ)
[][] (`μ α)   σ@(_ ▷ _) τ@(_ ▷ _) = cong `μ_ ([][] α (σ ↑ ▷ ∙) (τ ↑ ▷ ∙))
{-# REWRITE [][] #-}

left-id : (τ : Sub m n) → id ⨟ τ ≡ τ
left-id id      = refl
left-id (τ ↑)   = cong _↑ (left-id τ)
left-id (τ ▷ α) = refl
{-# REWRITE left-id #-}

assoc : (σ : Sub o p) (τ : Sub n o) (ν : Sub m n) → (σ ⨟ τ) ⨟ ν ≡ σ ⨟ (τ ⨟ ν)
assoc σ       τ         id = refl
assoc σ       τ         (ν ↑) = cong _↑ (assoc σ τ ν)
assoc σ       id        ν@(_ ▷ _) = refl
assoc σ       (τ ↑)     (ν ▷ _) = assoc σ τ ν
assoc id      τ@(_ ▷ _) ν@(_ ▷ _) = refl
assoc (σ ↑)   (τ ▷ _)   ν@(_ ▷ _) = assoc σ τ ν
assoc (σ ▷ α) τ@(_ ▷ _) ν@(_ ▷ _) = cong₂ _▷_ (assoc σ τ ν) refl
{-# REWRITE assoc #-}

--------------------------------------------------------------------------------
-- Interpreting descriptions

Env : ℕ → Set₁
Env zero    = Lift _ ⊤
Env (suc n) = Env n × Set

⟦_⟧_ : Reg n → Env n → Set
data μ (α : Reg (suc n)) (Γ : Env n) : Set

⟦ ∙      ⟧ (_ , A) = A
⟦ α ↑    ⟧ (Γ , _) = ⟦ α ⟧ Γ
⟦ `0     ⟧ Γ       = ⊥
⟦ α `+ β ⟧ Γ       = ⟦ α ⟧ Γ ⊎ ⟦ β ⟧ Γ
⟦ `1     ⟧ Γ       = ⊤
⟦ α `× β ⟧ Γ       = ⟦ α ⟧ Γ × ⟦ β ⟧ Γ
⟦ `μ α   ⟧ Γ       = μ α Γ

data μ α Γ where
  con : ⟦ α ⟧ (Γ , μ α Γ) → μ α Γ

--------------------------------------------------------------------------------

data Var : ℕ → Set where
  ∙  : Var (suc n)
  _↑ : Var n → Var (suc n)

∂[_]_ : Var n → Reg n → Reg n
∂[ x   ] `0       = `0
∂[ x   ] (α `+ β) = ∂[ x ] α `+ ∂[ x ] β
∂[ x   ] `1       = `0
∂[ x   ] (α `× β) = ∂[ x ] α `× β `+ α `× ∂[ x ] β
∂[ x   ] (`μ α)   = `μ ∂[ x ↑ ] α [ `μ α ]₀ ↑ `+
                       ∂[ ∙ ] α [ `μ α ]₀ ↑ `× ∙
∂[ ∙   ] ∙        = `1
∂[ _ ↑ ] ∙        = `0
∂[ ∙   ] (α ↑)    = `0
∂[ x ↑ ] (α ↑)    = ∂[ x ] α ↑

∂₀ : Reg (suc n) → Reg (suc n)
∂₀ α = ∂[ ∙ ] α

--------------------------------------------------------------------------------

listDesc : Reg (suc n)
listDesc = `μ `1 `+ ∙ ↑ `× ∙

list : Set → Set
list A = ⟦ listDesc ⟧ (lift tt , A)

pattern []       = con (inj₁ tt)
pattern _∷_ x xs = con (inj₂ (x , xs))

∂listDesc : Reg (suc n)
∂listDesc = ∂₀ listDesc

∂list : Set → Set
∂list A = ⟦ ∂listDesc ⟧ (lift tt , A)

pattern here xs    = con (inj₁ (inj₂ (inj₁ (_ , xs))))
pattern there x xs = con (inj₂ (inj₂ (inj₂ (x , _)) , xs))

∂list→list² : ∂list A → list A × list A
∂list→list² (here xs)    = [] , xs
∂list→list² (there x xs) = Product.map₁ (x ∷_) (∂list→list² xs)

list²→∂list : list A × list A → ∂list A
list²→∂list ([]     , ys) = here ys
list²→∂list (x ∷ xs , ys) = there x (list²→∂list (xs , ys))

list²→∂list→list² : (xs : ∂list A) → list²→∂list (∂list→list² xs) ≡ xs
list²→∂list→list² (here xs)    = refl
list²→∂list→list² (there x xs) = cong (there x) (list²→∂list→list² xs)

∂list→list²→∂list : (xs : list A × list A) → ∂list→list² (list²→∂list xs) ≡ xs
∂list→list²→∂list ([]     , ys) = refl
∂list→list²→∂list (x ∷ xs , ys) = cong (Product.map₁ (x ∷_)) (∂list→list²→∂list (xs , ys))

∂list↔list² : ∂list A ↔ (list A × list A)
∂list↔list² = mk↔ₛ′ ∂list→list² list²→∂list ∂list→list²→∂list list²→∂list→list²
