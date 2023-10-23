module list-fusion where

open import Level
open import Function using ( _∘_; const )
open import Data.Bool using ( Bool; true; false; if_then_else_; _∧_ )
open import Data.List using ( List; _∷_; []; foldl; foldr; map; scanl; scanr )
open import Data.Product using ( _×_; _,_; uncurry )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

module _ where
  -- Ref: https://wiki.portal.chalmers.se/agda/Libraries/LightweightFreeTheorems

  private
    variable
      ℓ ℓ' : Level

  [Set_] : ∀ ℓ → Set ℓ → Set ℓ → Set (suc ℓ)
  [Set ℓ ] A₁ A₂ = A₁ → A₂ → Set ℓ

  [Set₂] = [Set (suc (suc 0ℓ)) ]
  [Set₁] = [Set (suc 0ℓ) ]
  [Set] = [Set 0ℓ ]

  Π : (A : Set ℓ) (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
  Π A B = (a : A) → B a

  [Π] :
    ∀ {A₁ A₂ B₁ B₂} →
    ([A] : [Set ℓ ] A₁ A₂) →
    ([B] : ∀ {a₁ a₂} → [A] a₁ a₂ → [Set ℓ' ] (B₁ a₁) (B₂ a₂)) →
    [Set (ℓ ⊔ ℓ') ] (Π A₁ B₁) (Π A₂ B₂)
  [Π] [A] [B] f₁ f₂ = ∀ {a₁ a₂} [a] → [B] [a] (f₁ a₁) (f₂ a₂)

  _[→]_ :
    ∀ {A₁ A₂ B₁ B₂} →
    ([A] : [Set ℓ ] A₁ A₂) →
    ([B] : [Set ℓ' ] B₁ B₂) →
    [Set (ℓ ⊔ ℓ') ] (A₁ → B₁) (A₂ → B₂)
  [A] [→] [B] = [Π] [A] λ _ → [B]

  infixr 0 _[→]_

private
  variable
    A A₁ A₂ B C D : Set

-- type CList a = forall b. (a -> b -> b) -> b -> b
CList : Set → Set₁
CList A = Π Set λ B → (A → B → B) → B → B

-- Assuming parametricity
[CList] : [Set] A₁ A₂ → [Set₁] (CList A₁) (CList A₂)
[CList] [A] = [Π] [Set] λ [B] → ([A] [→] [B] [→] [B]) [→] [B] [→] [B]
postulate Parametricity-CList : ∀ (g : CList A) → [CList] _≡_ g g

build : CList A → List A
build {A = A} g = g (List A) _∷_ []

-- foldr/build

rule-foldr/build :
  ∀ (g : CList A) c n → foldr c n (build g) ≡ g B c n
rule-foldr/build g c n =
  Parametricity-CList g
    (λ x y → foldr c n x ≡ y)
    (λ where refl refl → refl)
    refl

-- map

mapFB : (A → C → C) → (B → A) → (B → C → C)
mapFB c f = λ x ys → c (f x) ys

rule-map :
  ∀ (f : A → B) xs → map f xs ≡ build (λ _ c n → foldr (mapFB c f) n xs)
rule-map f [] = refl
rule-map f (x ∷ xs) rewrite rule-map f xs = refl

-- point-wise
rule-mapList :
  ∀ (f : A → B) xs → foldr (mapFB _∷_ f) [] xs ≡ map f xs
rule-mapList f [] = refl
rule-mapList f (x ∷ xs) rewrite rule-mapList f xs = refl

rule-mapFB :
  ∀ (c : A → D → D) (f : B → A) (g : C → B) → mapFB (mapFB c f) g ≡ mapFB c (f ∘ g)
rule-mapFB c f g = refl

rule-mapFB/id :
  ∀ (c : A → B → B) → mapFB c (λ x → x) ≡ c
rule-mapFB/id c = refl

-- filter

filter : (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

filterFB : (A → B → B) → (A → Bool) → (A → B → B)
filterFB c p x r = if p x then c x r else r

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
rule-filterFB c p q a b with q a
... | true  = refl
... | false = refl

-- scanl

scanlFB : (B → A → B) → (B → C → C) → (A → (B → C) → (B → C))
scanlFB f c = λ b g x → let b' = f x b in c b' (g b')

rule-scanl :
  ∀ (f : B → A → B) a bs →
  scanl f a bs ≡ build (λ _ c n → c a (foldr (scanlFB f c) (const n) bs a))
rule-scanl f a [] = refl
rule-scanl f a (x ∷ bs) rewrite rule-scanl f (f a x) bs = refl

-- scanr

scanrFB : (A → B → B) → (B → C → C) → (A → B × C → B × C)
scanrFB f c x (r , est) = f x r , c r est

rule-scanr :
  ∀ (f : A → B → B) q0 ls →
  scanr f q0 ls ≡ build (λ _ c n → uncurry c (foldr (scanrFB f c) (q0 , n) ls))
rule-scanr f q0 [] = refl
rule-scanr f q0 (x ∷ ls) rewrite rule-scanr f q0 ls = refl

rule-scanrList :
  ∀ (f : A → B → B) q0 ls →
  uncurry _∷_ (foldr (scanrFB f _∷_) (q0 , []) ls) ≡ scanr f q0 ls
rule-scanrList f q0 [] = refl
rule-scanrList f q0 (x ∷ ls) with scanr f q0 ls | rule-scanr f q0 ls
... | y ∷ ls' | refl = refl
