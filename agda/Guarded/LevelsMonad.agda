{-# OPTIONS --cubical --guarded #-}

module Guarded.LevelsMonad where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Guarded.Prims

private
  variable
    ℓ : Level
    A B C : Type ℓ

infixl 1 _>>=_
infixr 3 _<|>_
infixl 4 _<*>_
infixr 5 _∷_ delay′_

--------------------------------------------------------------------------------
-- An alternative definition of Levels monad

-- List with an explicit "delay" constructor
data Levels (A : Type ℓ) : Type ℓ where
  []    : Levels A
  _∷_   : (x : A) (xs : Levels A) → Levels A
  delay : (xs : ▹ Levels A) → Levels A
  swap  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (Levels A)

delay′_ : Levels A → Levels A
delay′_ xs = delay (next xs)

--------------------------------------------------------------------------------
-- Eliminators

module Elim {a p} {A : Type a} {P : Levels A → Type p}
  ([]* : P [])
  (_∷*_ : ∀ x {xs} → P xs → P (x ∷ xs))
  (delay* : ∀ {xs} → ▸[ α ] P (xs α) → P (delay xs))
  (swap* : ∀ x y {xs} (xs* : P xs)
    → PathP (λ i → P (swap x y xs i)) (x ∷* (y ∷* xs*)) (y ∷* (x ∷* xs*)))
  (trunc* : ∀ xs → isSet (P xs))
  where

  f : ∀ xs → P xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (delay xs▹) = delay* λ α → f (xs▹ α)
  f (swap x y xs i) = swap* x y (f xs) i
  f (trunc xs ys p q i j) =
    isOfHLevel→isOfHLevelDep 2 trunc*
      (f xs) (f ys)
      (cong f p) (cong f q)
      (trunc xs ys p q) i j

module ElimProp {a p} {A : Type a} {P : Levels A → Type p}
  ([]* : P [])
  (_∷*_ : ∀ x {xs} → P xs → P (x ∷ xs))
  (delay* : ∀ {xs} → ▸[ α ] P (xs α) → P (delay xs))
  (PProp : ∀ xs → isProp (P xs))
  where

  f : ∀ xs → P xs
  f = Elim.f []* _∷*_ delay*
    (λ x y {xs} xs* → toPathP
      (PProp _
        (transport (λ i → P (swap x y xs i)) (x ∷* (y ∷* xs*)))
        (y ∷* (x ∷* xs*))))
    (λ xs → isProp→isSet (PProp xs))

module Rec {a b} {A : Type a} {B : Type b}
  ([]* : B)
  (_∷*_ : A → B → B)
  (delay* : ▹ B → B)
  (swap* : ∀ x y xs → x ∷* (y ∷* xs) ≡ y ∷* (x ∷* xs))
  (BSet : isSet B)
  where

  f : Levels A → B
  f = Elim.f []* (λ x xs → x ∷* xs) (λ xs → delay* xs) (λ x y xs → swap* x y xs) (λ _ → BSet)

-- Left biased, consume _∷_ first
module Elim2 {a b p} {A : Type a} {B : Type b} {P : Levels A → Levels B → Type p}
  ([]- : ∀ us → P [] us)
  (∷- : ∀ x {xs us} → P xs us → P (x ∷ xs) us)
  (delay[] : ∀ {xs} → ▸[ α ] P (xs α) [] → P (delay xs) [])
  (delay∷ : ∀ u {xs us} → P (delay xs) us → P (delay xs) (u ∷ us))
  (delayDelay : ∀ {xs us} → ▸[ α ] P (xs α) (us α) → P (delay xs) (delay us))
  (swap- : ∀ x y {xs us} (ih : P xs us)
    → PathP (λ i → P (swap x y xs i) us) (∷- x (∷- y ih)) (∷- y (∷- x ih)))
  (delaySwap : ∀ x y {xs ys} (ih : P (delay xs) ys)
    → PathP (λ i → P (delay xs) (swap x y ys i)) (delay∷ x (delay∷ y ih)) (delay∷ y (delay∷ x ih)))
  (trunc* : ∀ xs ys → isSet (P xs ys))
  where

  f : ∀ xs ys → P xs ys
  f [] ys = []- ys
  f (x ∷ xs) ys = ∷- x (f xs ys)
  f (delay xs) [] = delay[] λ α → f (xs α) []
  f (delay xs) (x ∷ ys) = delay∷ x (f (delay xs) ys)
  f (delay xs) (delay ys) = delayDelay λ α → f (xs α) (ys α)
  f (swap x y xs i) ys = swap- x y (f xs ys) i
  f (delay xs) (swap x y ys i) = delaySwap x y (f (delay xs) ys) i
  f (delay xs) (trunc ys zs p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ ws → trunc* (delay xs) ws)
      (f (delay xs) ys) (f (delay xs) zs)
      (cong (f (delay xs)) p) (cong (f (delay xs)) q)
      (trunc ys zs p q) i j
  f (trunc xs ys p q i j) zs =
    isOfHLevel→isOfHLevelDep 2 (λ ws → trunc* ws zs)
      (f xs zs) (f ys zs)
      (cong (flip f zs) p) (cong (flip f zs) q)
      (trunc xs ys p q) i j

module ElimProp2 {a b p} {A : Type a} {B : Type b} {P : Levels A → Levels B → Type p}
  ([]- : ∀ ys → P [] ys)
  (∷- : ∀ x {xs ys} → P xs ys → P (x ∷ xs) ys)
  (delay[] : ∀ {xs} → ▸[ α ] P (xs α) [] → P (delay xs) [])
  (delay∷ : ∀ x {xs ys} → P (delay xs) ys → P (delay xs) (x ∷ ys))
  (delayDelay : ∀ {xs ys} → ▸[ α ] P (xs α) (ys α) → P (delay xs) (delay ys))
  (PProp : ∀ xs ys → isProp (P xs ys))
  where

  f : ∀ xs ys → P xs ys
  f = Elim2.f []- ∷- delay[] delay∷ delayDelay
    (λ x y {xs} {ys} ih → toPathP
      (PProp _ _
        (transport (λ i → P (swap x y xs i) ys) (∷- x (∷- y ih)))
        (∷- y (∷- x ih))))
    (λ x y {xs} {ys} ih → toPathP
      (PProp _ _
        (transport (λ i → P (delay xs) (swap x y ys i)) (delay∷ x (delay∷ y ih)))
        (delay∷ y (delay∷ x ih))))
    (λ xs ys → isProp→isSet (PProp xs ys))

module Rec2 {a b c} {A : Type a} {B : Type b} {C : Type c}
  ([]- : Levels B → C)
  (∷- : A → C → C)
  (delay[] : ▹ C → C)
  (delay∷ : B → C → C)
  (delayDelay : ▹ C → C)
  (swap- : ∀ x y xs → ∷- x (∷- y xs) ≡ ∷- y (∷- x xs))
  (▹swap : ∀ x y xs → delay∷ x (delay∷ y xs) ≡ delay∷ y (delay∷ x xs))
  (CSet : isSet C)
  where

  f : Levels A → Levels B → C
  f = Elim2.f []- (λ x z → ∷- x z) (λ xs → delay[] xs) (λ x z → delay∷ x z) (λ z → delayDelay z)
    (λ x y z → swap- x y z) (λ x y z → ▹swap x y z)
    (λ _ _ → CSet)

--------------------------------------------------------------------------------
-- Lawful Functor, Applicative, Alternative, and Monad

map : (A → B) → Levels A → Levels B
map f = Rec.f [] (λ x → f x ∷_) delay (λ x y → swap (f x) (f y)) trunc

pure : A → Levels A
pure x = x ∷ []

guard : Bool → Levels Unit
guard b = if b then pure tt else []

_<|>_ : Levels A → Levels A → Levels A
_<|>_ = Rec2.f (idfun _) _∷_ delay _∷_ delay swap swap trunc

abstract

  <|>IdL : (xs : Levels A) → ([] <|> xs) ≡ xs
  <|>IdL xs = refl

  <|>IdR : (xs : Levels A) → (xs <|> []) ≡ xs
  <|>IdR = ElimProp.f
    refl
    (λ x → cong (x ∷_))
    (λ ih → cong delay (later-ext ih))
    (λ _ → trunc _ _)

  ∷<|>Interchange : (x : A) (xs ys : Levels A) → (x ∷ xs <|> ys) ≡ (xs <|> x ∷ ys)
  ∷<|>Interchange x = ElimProp2.f
    (λ _ → refl)
    (λ y {xs ys} ih → swap x y (xs <|> ys) ∙ cong (y ∷_) ih)
    (λ _ → refl)
    (λ _ _ → refl)
    (λ _ → refl)
    (λ _ _ → trunc _ _)

  <|>Comm : (xs ys : Levels A) → (xs <|> ys) ≡ (ys <|> xs)
  <|>Comm =
    ElimProp2.f
      (λ ys → sym (<|>IdR ys))
      (λ x {xs ys} eq → cong (x ∷_) eq ∙ ∷<|>Interchange x ys xs)
      (λ ih → cong delay (later-ext ih))
      (λ x → cong (x ∷_))
      (λ ih → cong delay (later-ext ih))
      (λ _ _ → trunc _ _)

  delayDistR<|> : (xs ys : ▹ Levels A) → delay (λ α → xs α <|> ys α) ≡ (delay xs <|> delay ys)
  delayDistR<|> xs ys = refl

  <|>Assoc : (xs ys zs : Levels A) → ((xs <|> ys) <|> zs) ≡ (xs <|> (ys <|> zs))
  <|>Assoc = ElimProp2.f
    (λ _ _ → refl)
    (λ x ih zs → cong (x ∷_) (ih zs))
    (λ {xs} _ zs → cong (_<|> zs) (<|>IdR (delay xs)))
    (λ y ih zs → cong (y ∷_) (ih zs))
    (λ {xs ys} ih → ElimProp.f
      (<|>IdR (delay xs <|> delay ys) ∙ cong (delay xs <|>_) (sym (<|>IdR (delay ys))))
      (λ x ih' → cong (x ∷_) ih')
      (λ {zs} _ → cong delay (later-ext λ α → ih α (zs α)))
      (λ _ → trunc _ _))
    (λ _ _ → isPropΠ λ _ → trunc _ _)

  <|>Swap : (xs ys zs : Levels A) → (xs <|> ys <|> zs) ≡ (ys <|> xs <|> zs)
  <|>Swap xs ys zs =
    sym (<|>Assoc xs ys zs) ∙∙
    cong (_<|> zs) (<|>Comm xs ys) ∙∙
    <|>Assoc ys xs zs


_>>=_ : Levels A → (A → Levels B) → Levels B
xs >>= k = Rec.f [] (λ x ys → k x <|> ys) delay (λ x y → <|>Swap (k x) (k y)) trunc xs

_>>_ : Levels A → Levels B → Levels B
xs >> ys = xs >>= λ _ → ys

_<*>_ : Levels (A → B) → Levels A → Levels B
fs <*> xs = do
  f <- fs
  x <- xs
  pure (f x)

abstract

  >>=IdL : (x : A) (h : A → Levels B) → (pure x >>= h) ≡ h x
  >>=IdL x h = <|>IdR (h x)

  >>=IdR : (xs : Levels A) → (xs >>= pure) ≡ xs
  >>=IdR = ElimProp.f
    refl
    (λ x → cong (x ∷_))
    (λ ih → cong delay (later-ext ih))
    (λ _ → trunc _ _)

  ▹>>=Commute : (xs : ▹ Levels A) (h : A → Levels B) → delay (λ α → xs α >>= h) ≡ (delay xs >>= h)
  ▹>>=Commute xs h = refl

  >>=DistL<|> : (xs ys : Levels A) (h : A → Levels B)
    → (xs <|> ys >>= h) ≡ ((xs >>= h) <|> (ys >>= h))
  >>=DistL<|> xs ys h = ElimProp2.f
    (λ _ → refl)
    (λ x {us vs} ih → cong (h x <|>_) ih ∙ sym (<|>Assoc (h x) (us >>= h) (vs >>= h)))
    (λ ih → cong delay (later-ext ih))
    (λ x {us vs} ih → cong (h x <|>_) ih ∙ <|>Swap (h x) (delay us >>= h) (vs >>= h))
    (λ ih → cong delay (later-ext ih))
    (λ us vs → trunc (us <|> vs >>= h) ((us >>= h) <|> (vs >>= h)))
    xs ys

  >>=Assoc : (xs : Levels A) (g : A → Levels B) (h : B → Levels C)
    → (xs >>= g >>= h) ≡ (xs >>= λ x → g x >>= h)
  >>=Assoc xs g h = ElimProp.f
    refl
    (λ x {ys} ih → >>=DistL<|> (g x) (ys >>= g) h ∙ cong ((g x >>= h) <|>_) ih)
    (λ ih → cong delay (later-ext ih))
    (λ ys → trunc (ys >>= g >>= h) (ys >>= λ y → g y >>= h))
    xs

--------------------------------------------------------------------------------
-- Example

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᵇ_; _==_ to _≡ᵇ_)

_ : ⦇ (1 ∷ delay′ 2 ∷ delay′ 3 ∷ []) , (1 ∷ delay′ 2 ∷ delay′ 3 ∷ []) ⦈
  ≡ (1 , 1) ∷ delay′
    (1 , 2) ∷ (2 , 1) ∷ delay′
    (1 , 3) ∷ (2 , 2) ∷ (3 , 1) ∷ delay′
    (2 , 3) ∷ (3 , 2) ∷ delay′
    (3 , 3) ∷ []
_ = refl

nats : Levels ℕ
nats = fix {A = ℕ → Levels ℕ} (λ f n → n ∷ delay λ α → f α (suc n)) 0

pyth : Levels (ℕ × ℕ × ℕ)
pyth = do
  x ← nats
  y ← nats
  z ← nats
  guard ((0 <ᵇ x) and (0 <ᵇ y) and (0 <ᵇ z))
  guard (x · x + y · y ≡ᵇ z · z)
  pure (x , y , z)
