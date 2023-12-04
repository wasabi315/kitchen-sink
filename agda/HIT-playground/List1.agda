{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Everything

infixr 5 _++_ _∷_ _∷'_

-- A bit unfamiliar definition of the list datatype
-- (Maybe) concatination is more efficient than the usual one
data List (A : Set) : Set where
  [] : List A
  [_] : A → List A
  _++_ : List A → List A → List A

  -- Quotienting the tree structure with the following laws
  ++-identityₗ : ∀ (xs : List A) → [] ++ xs ≡ xs
  ++-identityᵣ : ∀ (xs : List A) → xs ++ [] ≡ xs
  ++-assoc : ∀ (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs


-- fast cons
pattern _∷_ x xs = [ x ] ++ xs

mutual

  -- slow cons
  _∷'_ : ∀ {A} → A → List A → List A
  x ∷' [] = [ x ]
  x ∷' [ y ] = [ x ] ++ [ y ]
  x ∷' xs ++ ys = (x ∷' xs) ++ ys
  x ∷' ++-identityₗ xs i = ∷-∷' x xs i
  x ∷' ++-identityᵣ xs i = ++-identityᵣ (x ∷' xs) i
  x ∷' ++-assoc xs ys zs i = ++-assoc (x ∷' xs) ys zs i

  ∷-∷' : ∀ {A} (x : A) xs → x ∷ xs ≡ x ∷' xs
  ∷-∷' x [] = ++-identityᵣ [ x ]
  ∷-∷' x [ y ] = refl
  ∷-∷' x (xs ++ ys) = ++-assoc [ x ] xs ys ∙ cong (_++ ys) (∷-∷' x xs)
  ∷-∷' x (++-identityₗ xs i) = {!   !}
  ∷-∷' x (++-identityᵣ xs i) = {!   !}
  ∷-∷' x (++-assoc xs ys zs i) = {!   !}
