{-# OPTIONS --safe --cubical --guardedness #-}

open import Cubical.Codata.Stream.Base using ( Stream )
open import Cubical.Data.List.Base using ( List; []; _∷_ )
open import Cubical.Data.Sigma.Base using ( _×_; _,_; fst )
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using ( idfun; _∘_ )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open Stream

private
  variable
    A B C D : Type

--------------------------------------------------------------------------------
-- mealy machine

infixr 5 _⋙_

record Mealy (A B : Type) : Type where
  coinductive
  field
    step : A → B × Mealy A B

open Mealy

eat : Mealy A B → List A → List B
eat f [] = []
eat f (x ∷ xs) =
  let y , f' = step f x
   in y ∷ eat f' xs

eatω : Mealy A B → Stream A → Stream B
eatω f xs =
  let y , f' = step f (head xs)
   in λ { .head → y; .tail → eatω f' (tail xs) }

id : Mealy A A
step id x = x , id

_⋙_ : Mealy A B → Mealy B C → Mealy A C
step (f ⋙ g) x =
  let y , f' = step f x
      z , g' = step g y
   in z , f' ⋙ g'

arr : (A → B) → Mealy A B
step (arr f) x = f x , arr f

first : Mealy A B → Mealy (A × C) (B × C)
step (first f) (x , z) =
  let y , f' = step f x
   in (y , z) , first f'

map : (B → C) → Mealy A B → Mealy A C
step (map f g) x =
  let y , g' = step g x
   in f y , map f g'

--------------------------------------------------------------------------------
-- Category laws

⋙-identityₗ : ∀ (f : Mealy A B) → id ⋙ f ≡ f
step (⋙-identityₗ f i) x =
  let y , f' = step f x in y , ⋙-identityₗ f' i

⋙-identityᵣ : ∀ (f : Mealy A B) → f ⋙ id ≡ f
step (⋙-identityᵣ f i) x =
  let y , f' = step f x in y , ⋙-identityᵣ f' i

⋙-assoc : ∀ (f : Mealy A B) (g : Mealy B C) (h : Mealy C D)
  → (f ⋙ g) ⋙ h ≡ f ⋙ (g ⋙ h)
step (⋙-assoc f g h i) x =
  let y , f' = step f x
      z , g' = step g y
      w , h' = step h z
   in w , ⋙-assoc f' g' h' i

--------------------------------------------------------------------------------
-- Arrow laws

arr-id : arr (idfun A) ≡ id
step (arr-id i) x = x , arr-id i

arr-compose : ∀ (f : A → B) (g : B → C)
  → arr (g ∘ f) ≡ arr f ⋙ arr g
step (arr-compose f g i) x = g (f x) , arr-compose f g i

first-arr : ∀ (f : A → B)
  → first {C = C} (arr f) ≡ arr (λ (x , y) → f x , y)
step (first-arr f i) (x , y) = (f x , y) , first-arr f i

first-compose : ∀ (f : Mealy A B) (g : Mealy B C)
  → first {C = C} (f ⋙ g) ≡ first f ⋙ first g
step (first-compose f g i) (x , w) =
  let y , f' = step f x
      z , g' = step g y
   in (z , w) , first-compose f' g' i

first-⋙-arr : ∀ (f : Mealy A B)
  → first {C = C} f ⋙ arr fst ≡ arr fst ⋙ f
step (first-⋙-arr f i) (x , z) =
  let y , f' = step f x
   in y , first-⋙-arr f' i

--------------------------------------------------------------------------------
-- Functor laws

map-id : map {A = A} (idfun B) ≡ idfun (Mealy A B)
step (map-id i f) x =
  let y , f' = step f x in y , map-id i f'

map-map : ∀ (f : C → D) (g : B → C)
  → map {A = A} f ∘ map g ≡ map (f ∘ g)
step (map-map f g i h) x =
  let y , h' = step h x in f (g y) , map-map f g i h'

--------------------------------------------------------------------------------
-- bisimulation

Pointwise : (A → A → Type) → (B → B → Type) → (A × B → A × B → Type)
Pointwise R S (x , y) (x' , y') = R x x' × S y y'

infix 4 _≈_

record _≈_ (f g : Mealy A B) : Type where
  coinductive
  field
    step : ∀ (x : A) → Pointwise _≡_ _≈_ (step f x) (step g x)

open _≈_

bisim : ∀ {f g : Mealy A B} → f ≈ g → f ≡ g
step (bisim p i) x =
  let q , r = step p x
   in q i , bisim r i

misib : ∀ {f g : Mealy A B} → f ≡ g → f ≈ g
step (misib p) x =
  let q = cong (λ h → step h x) p
   in (λ i → fst (q i)) , misib (λ i → snd (q i))

iso1 : ∀ {f g : Mealy A B} (p : f ≈ g) → misib (bisim p) ≡ p
step (iso1 p i) x =
  let q , r = step p x
   in q , iso1 r i

iso2 : ∀ {f g : Mealy A B} (p : f ≡ g) → bisim (misib p) ≡ p
step (iso2 p i j) x =
  let q = cong (λ h → step h x) p
   in fst (q j) , iso2 (λ i → snd (q i)) i j

path≃bisim : ∀ {f g : Mealy A B} → (f ≡ g) ≃ (f ≈ g)
path≃bisim = isoToEquiv (iso misib bisim iso1 iso2)

path≡bisim : ∀ {f g : Mealy A B} → (f ≡ g) ≡ (f ≈ g)
path≡bisim = ua path≃bisim
