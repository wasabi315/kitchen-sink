{-# OPTIONS --guardedness #-}

module PatternMatch.PatternMatch where

open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.List as List using ( List; _∷_; [] )
open import Data.List.Relation.Unary.Any using ( Any; any? )
open import Data.List.Relation.Unary.All using ( All; _∷_; [] )
open import Data.Product using ( _,_; uncurry )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary renaming ( map′ to mapDec )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; cong₂ )

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
    _∣- : ∀ {p q v} → p ≼ v → p ∣ q ≼ v
    -∣_ : ∀ {p q v} → q ≼ v → p ∣ q ≼ v
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
      (λ { (inj₁ p≼v) → p≼v ∣-
         ; (inj₂ q≼v) → -∣ q≼v })
      (λ { (p≼v ∣-) → inj₁ p≼v
         ; (-∣ q≼v) → inj₂ q≼v })
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
  ≼-synth : (p : Pat α) → p ≼ synth p
  ≼-synth — = —≼ inh _
  ≼-synth (con c ps) = con c (≼*-synth* ps)
  ≼-synth (p ∣ q) = ≼-synth p ∣-

  ≼*-synth* : (ps : Pat* αs) → ps ≼* synth* ps
  ≼*-synth* [] = []
  ≼*-synth* (p ∷ ps) = ≼-synth p ∷ ≼*-synth* ps

--------------------------------------------------------------------------------

mutual
  ≼-only : (v : Val α) → only v ≼ v
  ≼-only (con c vs) = con c (≼*-only* vs)

  ≼*-only* : (vs : Val* αs) → only* vs ≼* vs
  ≼*-only* [] = []
  ≼*-only* (v ∷ vs) = ≼-only v ∷ ≼*-only* vs

mutual
  only-only : {v v' : Val α} → only v ≼ v' → v ≡ v'
  only-only {v = con c vs} {con .c vs'} (con .c hs) =
    cong (con c) (only*-only* hs)

  only*-only* : {vs vs' : Val* αs} → only* vs ≼* vs' → vs ≡ vs'
  only*-only* {vs = []} {[]} hs = refl
  only*-only* {vs = v ∷ vs} {v' ∷ vs'} (h ∷ hs) =
    cong₂ _∷_ (only-only h) (only*-only* hs)

--------------------------------------------------------------------------------

_ : match? exVal (exPat ∷ []) ≡ yes _
_ = refl
