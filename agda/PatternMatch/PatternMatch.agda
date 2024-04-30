{-# OPTIONS --guardedness #-}

module PatternMatch.PatternMatch where

open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.List as List using ( List; _∷_; [] )
open import Data.List.Relation.Unary.Any using ( Any; any? )
open import Data.List.Relation.Unary.All using ( All; _∷_; [] )
open import Data.Product using ( _,_; uncurry )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary renaming ( map′ to mapDec )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import PatternMatch.Pattern

private
  variable
    A B : Set
    α β : Ty
    αs βs : List Ty

--------------------------------------------------------------------------------

infix 4 _≼_ _≼*_ _≼?_ _≼*?_

mutual
  data _≼_ {α} : Pat α → Val α → Set where
    —≼_ : ∀ v → — ≼ v
    ∣₁ : ∀ {p q v} → p ≼ v → p ∣ q ≼ v
    ∣₂ : ∀ {p q v} → q ≼ v → p ∣ q ≼ v
    con : ∀ (c : Con α) {ps : Pat* (args α c)} {vs}
      → ps ≼* vs
      → con c ps ≼ con c vs

  data _≼*_ : Pat* αs → Val* αs → Set where
    [] : [] ≼* []
    _∷_ : ∀ {p : Pat α} {ps : Pat* αs} {v vs}
      → p ≼ v
      → ps ≼* vs
      → p ∷ ps ≼* v ∷ vs

mutual
  _≼?_ : (p : Pat α) (v : Val α) → Dec (p ≼ v)
  — ≼? v = yes (—≼ v)
  con c ps ≼? con c' vs with c ≟ c'
  ... | no ¬c≡c' = no λ { (con .c _) → ¬c≡c' refl }
  ... | yes refl = mapDec (con c) (λ { (con .c ps≼vs) → ps≼vs }) (ps ≼*? vs)
  p ∣ q ≼? v =
    mapDec
      (λ { (inj₁ p≼v) → ∣₁ p≼v
         ; (inj₂ q≼v) → ∣₂ q≼v })
      (λ { (∣₁ p≼v) → inj₁ p≼v
         ; (∣₂ q≼v) → inj₂ q≼v })
      (p ≼? v ⊎-dec q ≼? v)

  _≼*?_ : (ps : Pat* αs) (vs : Val* αs) → Dec (ps ≼* vs)
  [] ≼*? [] = yes []
  p ∷ ps ≼*? v ∷ vs =
    mapDec
      (uncurry _∷_)
      (λ { (p≼v ∷ ps≼vs) → p≼v , ps≼vs })
      (p ≼? v ×-dec ps ≼*? vs)

match? : (v : Val α) (ps : List (Pat α)) → Dec (Any (_≼ v) ps)
match? v = any? (_≼? v)

--------------------------------------------------------------------------------

mutual
  synth : Pat α → Val α
  synth — = inh _
  synth (con c ps) = con c (synth* ps)
  synth (p ∣ q) = synth p

  synth* : Pat* αs → Val* αs
  synth* [] = []
  synth* (p ∷ ps) = synth p ∷ synth* ps

mutual
  ≼-synth : (p : Pat α) → p ≼ synth p
  ≼-synth — = —≼ inh _
  ≼-synth (con c ps) = con c (≼*-synth* ps)
  ≼-synth (p ∣ q) = ∣₁ (≼-synth p)

  ≼*-synth* : (ps : Pat* αs) → ps ≼* synth* ps
  ≼*-synth* [] = []
  ≼*-synth* (p ∷ ps) = ≼-synth p ∷ ≼*-synth* ps
