module list-fusion where

open import Level
open import Function using ( _∘_; const )
open import Data.Bool using ( Bool; true; false; if_then_else_; _∧_ )
open import Data.List using ( List; _∷_; []; foldr; map; scanl )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

private
  variable
    ℓ ℓ' : Level
    A A₁ A₂ A₃ : Set ℓ
    B B₁ B₂ : Set ℓ'
    P₁ : A₁ → Set ℓ'
    P₂ : A₂ → Set ℓ'

module _ where
  -- Ref: https://wiki.portal.chalmers.se/agda/Libraries/LightweightFreeTheorems

  [Set_] : ∀ ℓ → Set ℓ → Set ℓ → Set (suc ℓ)
  [Set ℓ ] A₁ A₂ = A₁ → A₂ → Set ℓ

  [Set₂] = [Set (suc (suc 0ℓ)) ]
  [Set₁] = [Set (suc 0ℓ) ]
  [Set] = [Set 0ℓ ]

  Π : (A : Set ℓ) (P : A → Set ℓ') → Set (ℓ ⊔ ℓ')
  Π A P = (a : A) → P a

  [Π] :
    ([A] : [Set ℓ ] A₁ A₂) →
    ([P] : ∀ {a₁ a₂} → [A] a₁ a₂ → [Set ℓ' ] (P₁ a₁) (P₂ a₂)) →
    [Set (ℓ ⊔ ℓ') ] (Π A₁ P₁) (Π A₂ P₂)
  [Π] [A] [P] f₁ f₂ = ∀ {a₁ a₂} [a] → [P] [a] (f₁ a₁) (f₂ a₂)

  _[→]_ :
    ([A] : [Set ℓ ] A₁ A₂) →
    ([B] : [Set ℓ' ] B₁ B₂) →
    [Set (ℓ ⊔ ℓ') ] (A₁ → B₁) (A₂ → B₂)
  [A] [→] [B] = [Π] [A] λ _ → [B]

  infixr 0 _[→]_

-- list fusions

-- type CList a = forall b. (a -> b -> b) -> b -> b
CList : Set → Set₁
CList A = Π Set λ B → (A → B → B) → B → B

build : CList A → List A
build {A = A} g = g (List A) _∷_ []

mapFB : (A₁ → B → B) → (A₂ → A₁) → (A₂ → B → B)
mapFB c f = λ x ys → c (f x) ys

filter : (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

filterFB : (A → B → B) → (A → Bool) → (A → B → B)
filterFB c p x r = if p x then c x r else r

scanlFB : (B₁ → A → B₁) → (B₁ → B₂ → B₂) → (A → (B₁ → B₂) → (B₁ → B₂))
scanlFB f c = λ b g x → let b' = f x b in c b' (g b')

data [List] ([A] : [Set] A₁ A₂) : [Set] (List A₁) (List A₂) where
  [[]] : [List] [A] [] []
  [∷] : ([A] [→] [List] [A] [→] [List] [A]) _∷_ _∷_

[CList] : [Set] A₁ A₂ → [Set₁] (CList A₁) (CList A₂)
[CList] [A] = [Π] [Set] λ [B] → ([A] [→] [B] [→] [B]) [→] [B] [→] [B]

-- Assuming parametricity
postulate Parametricity-CList : ∀ (g : CList A) → [CList] _≡_ g g

rule-foldr/build :
  ∀ (g : CList A) c n → foldr c n (build g) ≡ g B c n
rule-foldr/build g c n =
  Parametricity-CList g
    (λ x y → foldr c n x ≡ y)
    (λ where refl refl → refl)
    refl

rule-map :
  ∀ (f : A₁ → A₂) xs → map f xs ≡ build (λ _ c n → foldr (mapFB c f) n xs)
rule-map f [] = refl
rule-map f (x ∷ xs) rewrite rule-map f xs = refl

-- point-wise
rule-mapList :
  ∀ (f : A₁ → A₂) xs → foldr (mapFB _∷_ f) [] xs ≡ map f xs
rule-mapList f [] = refl
rule-mapList f (x ∷ xs) rewrite rule-mapList f xs = refl

rule-mapFB :
  ∀ (c : A₁ → B → B) (f : A₂ → A₁) (g : A₃ → A₂) → mapFB (mapFB c f) g ≡ mapFB c (f ∘ g)
rule-mapFB c f g = refl

rule-mapFB/id :
  ∀ (c : A → B → B) → mapFB c (λ x → x) ≡ c
rule-mapFB/id c = refl

rule-filter :
  ∀ (p : A → Bool) xs → filter p xs ≡ build (λ _ c n → foldr (filterFB c p) n xs)
rule-filter p [] = refl
rule-filter p (x ∷ xs) rewrite rule-filter p xs with p x
... | true = refl
... | false = refl

-- point-wise
rule-filterList :
  ∀ (p : A → Bool) xs → foldr (filterFB _∷_ p) [] xs ≡ filter p xs
rule-filterList p [] = refl
rule-filterList p (x ∷ xs) rewrite rule-filterList p xs = refl

-- point-wise
rule-filterFB :
  ∀ (c : A → B → B) p q a b →
  filterFB (filterFB c p) q a b ≡ filterFB c (λ x → q x ∧ p x) a b
rule-filterFB c p q a b with q a | p a
... | true  | true  = refl
... | true  | false = refl
... | false | _     = refl
