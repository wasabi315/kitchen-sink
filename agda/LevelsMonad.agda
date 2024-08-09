{-# OPTIONS --cubical --exact-split #-}

module LevelsMonad where

open import Cubical.Foundations.Everything hiding ( empty )
open import Cubical.Data.Sigma using ( _×_; _,_ )

private
  variable
    ℓ : Level
    A B : Type ℓ

--------------------------------------------------------------------------------

module Bag where
  open import Cubical.HITs.FiniteMultiset
    using ( []; _∷_; [_]; comm; trunc; _++_; module Elim; module Rec; module ElimProp; comm-++; assoc-++ )
    renaming ( FMSet to Bag )
    public
  open import Cubical.HITs.FiniteMultiset

  map : (A → B) → Bag A → Bag B
  map f = Rec.f trunc [] (λ x → f x ∷_) (λ x y → comm (f x) (f y))

  pure : A → Bag A
  pure x = x ∷ []

  infixr 4 _<*>_
  _<*>_ : Bag (A → B) → Bag A → Bag B
  _<*>_ = Rec.f (isSet→ trunc)
    (λ _ → [])
    (λ f rec xs → map f xs ++ rec xs)
    (λ f g rec → funExt λ xs →
      map f xs ++ map g xs ++ rec xs    ≡⟨ assoc-++ (map f xs) _ _ ⟩
      (map f xs ++ map g xs) ++ rec xs  ≡⟨ cong (_++ rec xs) (comm-++ (map f xs) _) ⟩
      (map g xs ++ map f xs) ++ rec xs  ≡⟨ sym (assoc-++ (map g xs) _ _) ⟩
      map g xs ++ map f xs ++ rec xs    ∎)

--------------------------------------------------------------------------------

module Levels where
  open import Cubical.Data.List as List using ( List; []; _∷_ )
  open Bag using ( Bag; []; _∷_; [_] )

  Levels : Type ℓ → Type ℓ
  Levels A = List (Bag A)

  map : (A → B) → Levels A → Levels B
  map f = List.map (Bag.map f)

  pure : A → Levels A
  pure x = (x ∷ []) ∷ []

  empty : Levels A
  empty = []

  infixr 3 _<|>_
  _<|>_ : Levels A → Levels A → Levels A
  [] <|> yss = yss
  xss@(_ ∷ _) <|> [] = xss
  (xs ∷ xss) <|> (ys ∷ yss) = (xs Bag.++ ys) ∷ (xss <|> yss)

  <|>-comm : (xss yss : Levels A) → (xss <|> yss) ≡ (yss <|> xss)
  <|>-comm [] [] = refl
  <|>-comm [] (_ ∷ _) = refl
  <|>-comm (_ ∷ _) [] = refl
  <|>-comm (xs ∷ xss) (ys ∷ yss) = cong₂ _∷_ (Bag.comm-++ xs ys) (<|>-comm xss yss)

  <|>-assoc : (xss yss zss : Levels A) → (xss <|> yss <|> zss) ≡ ((xss <|> yss) <|> zss)
  <|>-assoc [] yss zss = refl
  <|>-assoc (xs ∷ xss) [] zss = refl
  <|>-assoc (xs ∷ xss) (ys ∷ yss) [] = refl
  <|>-assoc (xs ∷ xss) (ys ∷ yss) (zs ∷ zss) = cong₂ _∷_ (Bag.assoc-++ xs ys zs) (<|>-assoc xss yss zss)

  wrap : Levels A → Levels A
  wrap xss = [] ∷ xss

  choices : (A → Levels B) → Bag A → Levels B
  choices f = Bag.Rec.f (List.isOfHLevelList 0 Bag.trunc)
    []
    (λ x xss → f x <|> xss)
    (λ x y xss →
      (f x <|> f y <|> xss)  ≡⟨ <|>-assoc (f x) (f y) _ ⟩
      (f x <|> f y) <|> xss  ≡⟨ cong (_<|> xss) (<|>-comm (f x) (f y)) ⟩
      (f y <|> f x) <|> xss  ≡⟨ sym (<|>-assoc (f y) (f x) _) ⟩
      (f y <|> f x <|> xss)  ∎)

  infixl 4 _<*>_
  _<*>_ : Levels (A → B) → Levels A → Levels B
  [] <*> xs = []
  (fs ∷ fss) <*> xss = List.map (fs Bag.<*>_) xss <|> wrap (fss <*> xss)

  infixl 1 _>>=_
  _>>=_ : Levels A → (A → Levels B) → Levels B
  [] >>= k = empty
  xs ∷ xss >>= k = choices k xs <|> wrap (xss >>= k)

  _ : ⦇ ([ 1 ] ∷ [ 2 ] ∷ [ 3 ] ∷ []) , ([ 1 ] ∷ [ 2 ] ∷ [ 3 ] ∷ []) ⦈ ≡
      [ 1 , 1 ] ∷
      ((1 , 2) ∷ (2 , 1) ∷ []) ∷
      ((1 , 3) ∷ (2 , 2) ∷ (3 , 1) ∷ []) ∷
      ((2 , 3) ∷ (3 , 2) ∷ []) ∷
      [ 3 , 3 ] ∷
      []
  _ = refl
