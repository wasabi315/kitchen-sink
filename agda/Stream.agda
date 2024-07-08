{-# OPTIONS --cubical --guarded #-}

open import Cubical.Foundations.Everything
open import IrrLaterPrims
open import Cubical.Data.Nat

private
  variable
    ℓ : Level
    A B : Type ℓ

--------------------------------------------------------------------------------

infixr 5 _∷_

record Stream (A : Type ℓ) : Type ℓ where
  inductive
  eta-equality
  constructor _∷_
  field
    head : A
    tail▹ : ▹ Stream A

open Stream

fromFun : (ℕ → A) → Stream A
fromFun = fix λ f g → g 0 ∷ (f ⊛ next (g ∘ suc))

map-body : ▹ ((A → B) → Stream A → Stream B) → (A → B) → Stream A → Stream B
map-body map▹ f (x ∷ xs▹) = f x ∷ λ α → map▹ α f (xs▹ α)

map : (A → B) → Stream A → Stream B
map = fix map-body

map-eq : (f : A → B) (xs : Stream A)
  → map f xs ≡ f (head xs) ∷ map▹ (map f) (tail▹ xs)
map-eq f xs = fix-path map-body ≡$ f ≡$ xs

predict-body : ▹ (▹ Stream A → Stream (▹ A)) → ▹ Stream A → Stream (▹ A)
predict-body predict▹ xs▹ = (map▹ head xs▹) ∷ (predict▹ ⊛ map▹ tail▹ xs▹)

predict : ▹ Stream A → Stream (▹ A)
predict = fix predict-body

predict-eq : (xs▹ : ▹ Stream A)
  → predict xs▹ ≡ (map▹ head xs▹) ∷ (map▹ (predict ∘ tail▹) xs▹)
predict-eq xs▹ = fix-path predict-body ≡$ xs▹

predict⁻-body : ▹ (Stream (▹ A) → ▹ Stream A) → Stream (▹ A) → ▹ Stream A
predict⁻-body predict⁻▹ x▹s = map▹ _∷_ (head x▹s) ⊛ (predict⁻▹ ⊛ tail▹ x▹s)

predict⁻ : Stream (▹ A) → ▹ Stream A
predict⁻ = fix predict⁻-body

predict⁻-eq : (x▹s : Stream (▹ A))
  → predict⁻ x▹s ≡ (map▹ _∷_ (head x▹s) ⊛ (map▹ predict⁻ (tail▹ x▹s)))
predict⁻-eq x▹s = fix-path predict⁻-body ≡$ x▹s

predict⁻-predict : (xs▹ : ▹ Stream A) → predict⁻ (predict xs▹) ≡ xs▹
predict⁻-predict = fix λ ih▹ xs▹ →
    predict⁻ (predict xs▹)
  ≡⟨ congS predict⁻ (predict-eq xs▹) ⟩
    predict⁻ (map▹ head xs▹ ∷ (map▹ (predict ∘ tail▹) xs▹))
  ≡⟨ predict⁻-eq _ ⟩
    map▹ _∷_ (map▹ head xs▹) ⊛ (map▹ predict⁻ (map▹ (predict ∘ tail▹) xs▹))
  ≡⟨⟩
    map▹ _∷_ (map▹ head xs▹) ⊛ (next (predict⁻ ∘ predict) ⊛ map▹ tail▹ xs▹)
  ≡⟨ congS (λ p⁻∘p → map▹ _∷_ (map▹ head xs▹) ⊛ (p⁻∘p ⊛ map▹ tail▹ xs▹)) (later-ext λ α → funExt (ih▹ α)) ⟩
    map▹ _∷_ (map▹ head xs▹) ⊛ map▹ tail▹ xs▹
  ≡⟨⟩
    xs▹
  ∎

predict-predict⁻ : (x▹s : Stream (▹ A)) → predict (predict⁻ x▹s) ≡ x▹s
predict-predict⁻ = fix λ ih▹ x▹s →
    predict (predict⁻ x▹s)
  ≡⟨ congS predict (predict⁻-eq _) ⟩
    predict (map▹ _∷_ (head x▹s) ⊛ (map▹ predict⁻ (tail▹ x▹s)))
  ≡⟨ predict-eq _ ⟩
    (map▹ head (map▹ _∷_ (head x▹s) ⊛ (map▹ predict⁻ (tail▹ x▹s)))) ∷
    (map▹ (predict ∘ tail▹) (map▹ _∷_ (head x▹s) ⊛ (map▹ predict⁻ (tail▹ x▹s))))
  ≡⟨⟩
    head x▹s ∷
    (map▹ (predict ∘ tail▹) (map▹ _∷_ (head x▹s) ⊛ (map▹ predict⁻ (tail▹ x▹s))))
  ≡⟨⟩
    head x▹s ∷ (next (predict ∘ predict⁻) ⊛ tail▹ x▹s)
  ≡⟨ congS (λ p∘p⁻ → head x▹s ∷ (p∘p⁻ ⊛ tail▹ x▹s)) (later-ext λ α → funExt (ih▹ α)) ⟩
    head x▹s ∷ tail▹ x▹s
  ≡⟨⟩
    x▹s
  ∎

▹StreamIsoStream▹ : Iso (▹ Stream A) (Stream (▹ A))
▹StreamIsoStream▹ = iso predict predict⁻ predict-predict⁻ predict⁻-predict

▹Stream≃Stream▹ : (▹ Stream A) ≃ Stream (▹ A)
▹Stream≃Stream▹ = isoToEquiv ▹StreamIsoStream▹

▹Stream≡Stream▹ : (▹ Stream A) ≡ Stream (▹ A)
▹Stream≡Stream▹ = ua ▹Stream≃Stream▹

predict-next : (xs : Stream A) → predict (next xs) ≡ map next xs
predict-next = fix λ ih▹ xs →
    predict (next xs)
  ≡⟨ predict-eq _ ⟩
    map▹ head (next xs) ∷ map▹ (predict ∘ tail▹) (next xs)
  ≡⟨⟩
    next (head xs) ∷ (λ α → predict (tail▹ xs))
  ≡⟨⟩
    next (head xs) ∷ (λ α → predict (next (tail▹ xs) α))
  ≡⟨⟩
    next (head xs) ∷ (map▹ (predict ∘ next) (tail▹ xs))
  ≡⟨⟩
    next (head xs) ∷ (next (predict ∘ next) ⊛ tail▹ xs)
  ≡⟨ congS (λ pn → next (head xs) ∷ (pn ⊛ tail▹ xs)) (later-ext λ α → funExt (ih▹ α)) ⟩
    next (head xs) ∷ map▹ (map next) (tail▹ xs)
  ≡⟨ sym (map-eq _ _) ⟩
    map next xs
  ∎

predict⁻-next : (xs : Stream A) → predict⁻ (map next xs) ≡ next xs
predict⁻-next xs =
  predict⁻ (map next xs)        ≡⟨ congS predict⁻ (sym (predict-next xs)) ⟩
  predict⁻ (predict (next xs))  ≡⟨ predict⁻-predict _ ⟩
  next xs                       ∎
