{-# OPTIONS --cubical --guarded #-}

module Guarded.Stream where

open import Cubical.Foundations.Everything hiding ( extend )
open import Cubical.Data.Nat

open import Guarded.IrrPrims

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

repeat : A → Stream A
repeat x = fix (x ∷_)

iterate-body : ▹ ((A → ▹ A) → A → Stream A) → (A → ▹ A) → A → Stream A
iterate-body iterate▹ f x = x ∷ (iterate▹ ⊛ next f ⊛ f x)

iterate : (A → ▹ A) → A → Stream A
iterate = fix iterate-body

iterate-eq : (f : A → ▹ A) (x : A)
  → iterate f x ≡ x ∷ (map▹ (iterate f) (f x))
iterate-eq f x = fix-path iterate-body ≡$ f ≡$ x

--------------------------------------------------------------------------------

map-body : ▹ ((A → B) → Stream A → Stream B) → (A → B) → Stream A → Stream B
map-body map▹ f (x ∷ xs▹) = f x ∷ λ α → map▹ α f (xs▹ α)

map : (A → B) → Stream A → Stream B
map = fix map-body

map-eq : (f : A → B) (xs : Stream A)
  → map f xs ≡ f (head xs) ∷ map▹ (map f) (tail▹ xs)
map-eq f xs = fix-path map-body ≡$ f ≡$ xs

duplicate-body : ▹ (Stream A → Stream (Stream A)) → Stream A → Stream (Stream A)
duplicate-body duplicate▹ xs = xs ∷ (duplicate▹ ⊛ tail▹ xs)

duplicate : Stream A → Stream (Stream A)
duplicate = fix duplicate-body

duplicate-eq : (xs : Stream A)
  → duplicate xs ≡ xs ∷ (map▹ duplicate (tail▹ xs))
duplicate-eq xs = fix-path duplicate-body ≡$ xs

extend : (Stream A → B) → Stream A → Stream B
extend f xs = map f (duplicate xs)

extend-eq : (f : Stream A → B) (xs : Stream A)
  → extend f xs ≡ f xs ∷ (map▹ (extend f) (tail▹ xs))
extend-eq f xs =
    extend f xs
  ≡⟨⟩
    map f (duplicate xs)
  ≡⟨ congS (map f) (duplicate-eq xs) ⟩
    map f (xs ∷ (map▹ duplicate (tail▹ xs)))
  ≡⟨ map-eq f _ ⟩
    f xs ∷ map▹ (map f ∘ duplicate) (tail▹ xs)
  ≡⟨⟩
    f xs ∷ (map▹ (extend f) (tail▹ xs))
  ∎

--------------------------------------------------------------------------------

<*>-body : ▹ (Stream (A → B) → Stream A → Stream B) → Stream (A → B) → Stream A → Stream B
<*>-body <*>▹ (f ∷ fs▹) (x ∷ xs▹) = f x ∷ (<*>▹ ⊛ fs▹ ⊛ xs▹)

_<*>_ : Stream (A → B) → Stream A → Stream B
_<*>_ = fix <*>-body

<*>-eq : (fs : Stream (A → B)) (xs : Stream A)
  → fs <*> xs ≡ head fs (head xs) ∷ (map▹ _<*>_ (tail▹ fs) ⊛ tail▹ xs)
<*>-eq fs xs = fix-path <*>-body ≡$ fs ≡$ xs

--------------------------------------------------------------------------------

predict-body : ▹ (▹ Stream A → Stream (▹ A)) → ▹ Stream A → Stream (▹ A)
predict-body predict▹ xs▹ = (map▹ head xs▹) ∷ (predict▹ ⊛ map▹ tail▹ xs▹)

predict : ▹ Stream A → Stream (▹ A)
predict = fix predict-body

predict-eq : (xs▹ : ▹ Stream A)
  → predict xs▹ ≡ (map▹ head xs▹) ∷ (map▹ (predict ∘ tail▹) xs▹)
predict-eq xs▹ = fix-path predict-body ≡$ xs▹

--------------------------------------------------------------------------------

cfix-body : (Stream (▹ A) → A) → ▹ Stream A → Stream A
cfix-body f = extend f ∘ predict

cfix : (Stream (▹ A) → A) → Stream A
cfix f = fix (cfix-body f)

cfix-eq : (f : Stream (▹ A) → A)
  → cfix f ≡ extend f (predict (next (cfix f)))
cfix-eq f = fix-path (cfix-body f)

wfix-body : ▹ (Stream (Stream (▹ A) → A) → A) → Stream (Stream (▹ A) → A) → A
wfix-body wfix▹ xs = head xs (predict (map▹ (flip extend xs) wfix▹))

wfix : Stream (Stream (▹ A) → A) → A
wfix = fix wfix-body

wfix-eq : (w : Stream (Stream (▹ A) → A))
  → wfix w ≡ head w (predict (next (extend wfix w)))
wfix-eq w = fix-path wfix-body ≡$ w

kfix-body : Stream (Stream (▹ A) → A) → ▹ Stream A → Stream A
kfix-body w xs▹ = w <*> duplicate (predict xs▹)

kfix : Stream (Stream (▹ A) → A) → Stream A
kfix w = fix (kfix-body w)

kfix-eq : (w : Stream (Stream (▹ A) → A))
  → kfix w ≡ w <*> duplicate (predict (next (kfix w)))
kfix-eq w = fix-path (kfix-body w)

--------------------------------------------------------------------------------
-- predict is an isomorphism

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

--------------------------------------------------------------------------------

kfix-head : (w : Stream (Stream (▹ A) → A))
  → head (kfix w) ≡ head w (predict (next (kfix w)))
kfix-head w =
    head (kfix w)
  ≡⟨ cong head (kfix-eq w) ⟩
    head (w <*> duplicate (predict (next (kfix w))))
  ≡⟨ {!   !} ⟩
    {!   !}

kfix-tail▹ : (w : Stream (Stream (▹ A) → A))
  → ▸[ α ] tail▹ (kfix w) α ≡ kfix (tail▹ w α)
kfix-tail▹ w = {!   !}

kfix-wfix : (w : Stream (Stream (▹ A) → A)) → kfix w ≡ extend wfix w
kfix-wfix = fix λ ih▹ w →
    kfix w
  ≡⟨⟩
    head (kfix w) ∷ tail▹ (kfix w)
  ≡⟨ kfix-eq w ⟩
    w <*> duplicate (predict (next (kfix w)))
  ≡⟨ <*>-eq w _ ⟩
    head w (head (duplicate (predict (next (kfix w))))) ∷
    (λ α → tail▹ w α <*> tail▹ (duplicate (predict (next (kfix w)))) α)
  ≡⟨ {!   !} ⟩
    head w (head (duplicate (predict (next (kfix w))))) ∷
    (λ α → tail▹ w α <*> duplicate (tail▹ (predict (next (kfix w))) α))
  ≡⟨ {!   !} ⟩
    head w (head (duplicate (predict (next (kfix w))))) ∷
    (λ α → tail▹ w α <*> duplicate (predict (tail▹ (kfix w))))
  ≡⟨ {!   !} ⟩
    head w (predict (next (kfix w))) ∷
    (λ α → tail▹ w α <*> duplicate (predict (next (kfix (tail▹ w α)))))
  ≡⟨⟩
    head w (head (duplicate (predict (next (kfix w))))) ∷
    (λ α → tail▹ w α <*> duplicate (predict (next (kfix (tail▹ w α)))))
  ≡⟨ cong (head w (predict (next (kfix w))) ∷_) (later-ext λ α → sym (kfix-eq (tail▹ w α))) ⟩
    head w (predict (next (kfix w))) ∷ map▹ kfix (tail▹ w)
  ≡⟨ cong₂ _∷_
      (cong (head w ∘ predict) (later-ext λ α → ih▹ α w))
      (later-ext λ α → funExt (ih▹ α) ≡$ tail▹ w α)
   ⟩
    head w (predict (next (extend wfix w))) ∷ map▹ (extend wfix) (tail▹ w)
  ≡⟨ cong (_∷ _) (sym (wfix-eq w)) ⟩
    wfix w ∷ map▹ (extend wfix) (tail▹ w)
  ≡⟨ sym (extend-eq wfix w) ⟩
    extend wfix w
  ∎

--  fs <*> xs ≡ head fs (head xs) ∷ (map▹ _<*>_ (tail▹ fs) ⊛ tail▹ xs)
--  predict xs▹ ≡ (map▹ head xs▹) ∷ (map▹ (predict ∘ tail▹) xs▹)
