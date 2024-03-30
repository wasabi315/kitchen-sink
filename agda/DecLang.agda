{-# OPTIONS --cubical --guardedness #-}

module DecLang where

open import Cubical.Foundations.Everything
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Codata.Guarded.M
open import Data.Container.Core

private
  variable
    A B : Set

--------------------------------------------------------------------------------

_IsFixpointOf_ : Type → (Type → Type) → Type₁
X IsFixpointOf F = X ≡ F X

--------------------------------------------------------------------------------

unrollList : List A → Unit ⊎ (A × List A)
unrollList [] = inl tt
unrollList (x ∷ xs) = inr (x , xs)

rollList : Unit ⊎ (A × List A) → List A
rollList (inl tt) = []
rollList (inr (x , xs)) = x ∷ xs

rollList∘unrollList : ∀ (xs : List A) → rollList (unrollList xs) ≡ xs
rollList∘unrollList [] = refl
rollList∘unrollList (x ∷ xs) = refl

unrollList∘rollList : ∀ (xs : Unit ⊎ (A × List A)) → unrollList (rollList xs) ≡ xs
unrollList∘rollList (inl tt) = refl
unrollList∘rollList (inr (x , xs)) = refl

UnrollList : List A ≡ Unit ⊎ (A × List A)
UnrollList = isoToPath (iso unrollList rollList unrollList∘rollList rollList∘unrollList)

lemma : (List A → Bool) IsFixpointOf (λ X → Bool × (A → X))
lemma {A} =
  (List A → Bool)                      ≡⟨ cong (λ A → (A → Bool)) UnrollList ⟩
  (Unit ⊎ (A × List A) → Bool)         ≡⟨ ua Π⊎≃ ⟩
  (Unit → Bool) × (A × List A → Bool)  ≡⟨ cong₂ _×_ (UnitToTypePath Bool) (ua curryEquiv) ⟩
  Bool × (A → List A → Bool)           ∎

∅ : List A → Bool
∅ xs = false

ε : List A → Bool
ε [] = true
ε (_ ∷ _) = false

_ : ∀ A → PathP (λ i → lemma {A} i) ∅ (false , λ _ → ∅)
_ = λ A i → transp (λ j → lemma {A} (i ∧ j)) (~ i) ∅

--------------------------------------------------------------------------------

record Lang (A : Type) : Type where
  coinductive
  field
    ν : Bool
    δ : A → Lang A

open Lang

_∋_ : Lang A → List A → Bool
l ∋ [] = ν l
l ∋ (x ∷ xs) = δ l x ∋ xs

unrollLang : Lang A → Bool × (A → Lang A)
fst (unrollLang l) = ν l
snd (unrollLang l) = δ l

rollLang : Bool × (A → Lang A) → Lang A
ν (rollLang l) = fst l
δ (rollLang l) = snd l

rollLang∘unrollLang : (l : Lang A) → rollLang (unrollLang l) ≡ l
ν (rollLang∘unrollLang l i) = ν l
δ (rollLang∘unrollLang l i) = δ l

unrollLang∘rollLang : (l : Bool × (A → Lang A)) → unrollLang (rollLang l) ≡ l
fst (unrollLang∘rollLang l i) = fst l
snd (unrollLang∘rollLang l i) = snd l

UnrollLang : Lang A IsFixpointOf (λ X → Bool × (A → X))
UnrollLang = isoToPath (iso unrollLang rollLang unrollLang∘rollLang rollLang∘unrollLang)

--------------------------------------------------------------------------------

∋⁻ : (List A → Bool) → Lang A
ν (∋⁻ a) = a []
δ (∋⁻ a) x = ∋⁻ (a ∘ _∷_ x)

∋∘∋⁻ : ∀ (a : List A → Bool) → _∋_ (∋⁻ a) ≡ a
∋∘∋⁻ a i [] = a []
∋∘∋⁻ a i (x ∷ xs) = ∋∘∋⁻ (a ∘ _∷_ x) i xs

∋⁻∘∋ : ∀ (l : Lang A) → ∋⁻ (_∋_ l) ≡ l
ν (∋⁻∘∋ l i) = ν l
δ (∋⁻∘∋ l i) x = ∋⁻∘∋ (δ l x) i

[List→Bool]≡Lang : ∀ A → (List A → Bool) ≡ Lang A
[List→Bool]≡Lang A = isoToPath (iso ∋⁻ _∋_ ∋⁻∘∋ ∋∘∋⁻)

infixl 10 _+_ _+′_

_+_ : Lang A → Lang A → Lang A
ν (a + b) = ν a or ν b
δ (a + b) x = δ a x + δ b x

_+′_ : Lang A → Lang A → Lang A
_+′_ {A} = transport
  (λ i → [List→Bool]≡Lang A i → [List→Bool]≡Lang A i → [List→Bool]≡Lang A i)
  (λ a b xs → a xs or b xs)

νp : PathP (λ i → [List→Bool]≡Lang A i → Bool) (_$ []) ν
νp {A} i = transp (λ j → [List→Bool]≡Lang A (i ∨ ~ j) → Bool) i ν

δp : PathP (λ i → [List→Bool]≡Lang A i → A → [List→Bool]≡Lang A i) (λ f x → f ∘ _∷_ x) δ
δp {A} i a x =
  glue
    (λ { (i = i0) → a ∘ _∷_ x; (i = i1) → δ a x })
    (hcomp
      (λ j → λ { (i = i0) → ∋⁻ (a ∘ _∷_ x); (i = i1) → δ a x })
      (δ (unglue (i ∨ ~ i) a) x))

infixl 10 unionp
unionp : PathP
  (λ i → [List→Bool]≡Lang A i → [List→Bool]≡Lang A i → [List→Bool]≡Lang A i)
  (λ a b xs → a xs or b xs)
  _+′_
unionp = toPathP refl

syntax unionp i a b = a +[ i ] b

lemma₁ : ∀ (a b : Lang A) → ν (a +′ b) ≡ ν a or ν b
lemma₁ {A} =
  transport
    (λ i
      → (a b : [List→Bool]≡Lang A i)
      → νp i (a +[ i ] b) ≡ νp i a or νp i b)
    (λ a b → refl)

lemma₂ : ∀ (a b : Lang A) x → δ (a +′ b) x ≡ δ a x +′ δ b x
lemma₂ {A} =
  transport
    (λ i
      → ∀ (a b : [List→Bool]≡Lang A i) (x : A)
      → δp i (a +[ i ] b) x ≡ δp i a x +[ i ] δp i b x)
    (λ a b x → refl)

+≡+′ : ∀ (a b : Lang A) → a + b ≡ a +′ b
ν (+≡+′ {A} a b i) = lemma₁ a b (~ i)
δ (+≡+′ a b i) x = {!   !} -- (congS δ (+≡+′ a b) ≡$ x) i -- (+≡+′ (δ a x) (δ b x) ∙ sym (lemma₂ a b x)) i
