{-# OPTIONS --cubical --guardedness --safe #-}

--------------------------------------------------------------------------------
-- Proving dropping the same element from two FMSets preserves the path without
-- assuming A is discrete.
--
--   drop-∷ : (x : A) (xs ys : FMSet A) → x ∷ xs ≡ x ∷ ys → xs ≡ ys
--
-- This is tricky (at least for me) because we cannot just do `cong tail`.
-- `tail` is not definable for FMSet as it does not respect the comm path constructor.
--
-- The only way I came up with is the following flow:
--   1: Define the permutation relation _↭_ between lists.
--   2: Prove a version of drop-∷ for List A / _↭_
--   3: Prove Iso (FMSet A) (List A / _↭_)
--   4: Transport drop-∷ to FMSet.
--------------------------------------------------------------------------------

module MultisetDrop where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels using (isProp→)
open import Cubical.Foundations.Isomorphism using
  (Iso; iso; isoToEquiv; isoToPath; transportIsoToPath; transportIsoToPath⁻)
open import Cubical.Foundations.Univalence using (ua; uaβ; ~uaβ)
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.List as List using (List; []; _∷_; _++_; module ListPath)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.HITs.FiniteMultiset as FMSet using (FMSet; []; _∷_; comm; trunc)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/; squash/)
open import Cubical.Relation.Binary using (module BinaryRelation)

open BinaryRelation
open Iso

private
  variable
    ℓ : Level
    A : Type ℓ

infix  4 _∣↭∣_
infixr 5 _∷↭_

--------------------------------------------------------------------------------
-- Permutation relation
-- Ref: https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Relation/Binary/Permutation/Setoid/Properties.agda

module _ {A : Type ℓ} where
  infix  4 _↭_ _↭′_ _↭″_
  infixr 5 _↭-∷_

  data _↭_ (xs ys : List A) : Type ℓ
  _↭′_ _↭″_ : List A → List A → Type ℓ
  Comm : A → A → List A → List A → Type ℓ

  data _↭_ xs ys where
    con : xs ↭′ ys → xs ↭ ys

  xs ↭′ ys = (xs ↭″ ys) ⊎ (Σ[ zs ∈ _ ] (xs ↭ zs) × (zs ↭ ys))

  [] ↭″ [] = Unit*
  [] ↭″ y ∷ ys = ⊥*
  x ∷ xs ↭″ [] = ⊥*
  x ∷ xs ↭″ y ∷ ys = ((x ≡ y) × (xs ↭ ys)) ⊎ Comm x y xs ys

  Comm x y [] _ = ⊥*
  Comm x y (x' ∷ xs) [] = ⊥*
  Comm x y (x' ∷ xs) (y' ∷ ys) = (x ≡ y') × (x' ≡ y) × (xs ↭ ys)

  pattern ↭-[] = con (inl tt*)
  pattern _↭-∷_ p q = con (inl (inl (p , q)))
  pattern ↭-trans {zs} p q = con (inr (zs , p , q))
  pattern ↭-comm p q r = con (inl (inr (p , q , r)))

  _ : [] ↭ []
  _ = ↭-[]

  _ : ∀ {x y xs ys} → x ≡ y → xs ↭ ys → x ∷ xs ↭ y ∷ ys
  _ = _↭-∷_

  _ : ∀ {xs ys zs} → xs ↭ ys → ys ↭ zs → xs ↭ zs
  _ = ↭-trans

  _ : ∀ {x x' y y' xs ys} →
    x ≡ y' →
    x' ≡ y →
    xs ↭ ys →
    x ∷ x' ∷ xs ↭ y ∷ y' ∷ ys
  _ = ↭-comm

  ↭-refl : ∀ {xs} → xs ↭ xs
  ↭-refl {xs = []} = ↭-[]
  ↭-refl {xs = x ∷ xs} = refl ↭-∷ ↭-refl

  ↭-sym : ∀ {xs ys} → xs ↭ ys → ys ↭ xs
  ↭-sym (↭-trans p q) = ↭-trans (↭-sym q) (↭-sym p)
  ↭-sym {xs = []} {ys = []} ↭-[] = ↭-[]
  ↭-sym {xs = x ∷ xs} {ys = y ∷ ys} (p ↭-∷ q) = sym p ↭-∷ ↭-sym q
  ↭-sym {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (↭-comm p q r) =
    ↭-comm (sym q) (sym p) (↭-sym r)

  shift : ∀ {x y} → x ≡ y → ∀ xs ys → x ∷ xs ++ ys ↭ xs ++ y ∷ ys
  shift p [] ys = p ↭-∷ ↭-refl
  shift p (x ∷ xs) ys =
    ↭-trans (↭-comm refl refl ↭-refl) (refl ↭-∷ shift p xs ys)

  split-helper : ∀ {x} xs ys as bs →
    xs ↭ ys →
    ListPath.Cover ys (as ++ x ∷ bs) →
    Σ[ ps ∈ _ ] Σ[ qs ∈ _ ]
      ListPath.Cover xs (ps ++ x ∷ qs) × (ps ++ qs ↭ as ++ bs)
  split-helper xs ys as bs (↭-trans p q) eq
    using ps , qs , eq' , r ← split-helper _ ys as bs q eq
    using ps' , qs' , eq'' , s ← split-helper xs _ ps qs p eq'
    = ps' , qs' , eq'' , ↭-trans s r
  split-helper [] [] [] bs ↭-[] ()
  split-helper [] [] (_ ∷ _) bs ↭-[] ()
  split-helper (x ∷ xs) (y ∷ ys) [] bs (p ↭-∷ q) (eq , eq') =
    [] , xs ,
    (p ∙ eq , ListPath.reflCode xs) ,
    ↭-trans q (subst (ys ↭_) (ListPath.decode ys bs eq') ↭-refl)
  split-helper (x ∷ xs) (y ∷ ys) (a ∷ as) bs (p ↭-∷ q) (eq , eq')
    using ps , qs , eq' , r ← split-helper xs ys as bs q eq'
    = a ∷ ps , qs , (p ∙ eq , eq') , refl ↭-∷ r
  split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') [] (b ∷ _) (↭-comm p q r) (eq , eq' , eq'') =
    b ∷ [] , xs ,
    (p ∙ eq' , q ∙ eq , ListPath.reflCode xs) ,
    refl ↭-∷ ↭-trans r (subst (xs' ↭_) (ListPath.decode xs' _ eq'') ↭-refl)
  split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') (a ∷ []) bs (↭-comm p q r) (eq , eq' , eq'') =
    [] , a ∷ xs ,
    (p ∙ eq' , q ∙ eq , ListPath.reflCode xs) ,
    refl ↭-∷ ↭-trans r (subst (xs' ↭_) (ListPath.decode xs' _ eq'') ↭-refl)
  split-helper (x ∷ y ∷ xs) (x' ∷ y' ∷ xs') (a ∷ b ∷ as) bs (↭-comm p q r) (eq , eq' , eq'')
    using ps , qs , eq''' , s ← split-helper xs xs' as bs r eq''
    = b ∷ a ∷ ps , qs ,
      (p ∙ eq' , q ∙ eq , eq''') ,
      ↭-comm refl refl s

  split : ∀ {x xs ys zs} → xs ↭ (ys ++ x ∷ zs) →
    Σ[ ps ∈ _ ] Σ[ qs ∈ _ ]
      ListPath.Cover xs (ps ++ x ∷ qs) × (ps ++ qs ↭ ys ++ zs)
  split {x = x} {xs = xs} {ys = ys} {zs = zs} p =
    split-helper xs (ys ++ x ∷ zs) ys zs p (ListPath.reflCode _)

  ↭-dropMiddleElement-Cover : ∀ {x} ws xs {ys zs} →
    ListPath.Cover (ws ++ x ∷ ys) (xs ++ x ∷ zs) →
    ws ++ ys ↭ xs ++ zs
  ↭-dropMiddleElement-Cover [] [] (_ , eq) =
    subst (_ ↭_) (ListPath.decode _ _ eq) ↭-refl
  ↭-dropMiddleElement-Cover [] (x ∷ xs) (eq , eq') =
    ↭-trans
      (subst (_ ↭_) (ListPath.decode _ _ eq') ↭-refl)
      (↭-sym (shift (sym eq) xs _))
  ↭-dropMiddleElement-Cover (w ∷ ws) [] (eq , eq') =
    ↭-trans
      (shift eq ws _)
      (subst (_ ↭_) (ListPath.decode _ _ eq') ↭-refl)
  ↭-dropMiddleElement-Cover (w ∷ ws) (x ∷ xs) (eq , eq') =
    eq ↭-∷ ↭-dropMiddleElement-Cover ws xs eq'

  ↭-dropMiddleElement : ∀ {x} ws xs {ys zs} →
    ws ++ x ∷ ys ↭ xs ++ x ∷ zs →
    ws ++ ys ↭ xs ++ zs
  ↭-dropMiddleElement ws xs p
    using ps , qs , eq , q ← split p
    = ↭-trans (↭-dropMiddleElement-Cover ws ps eq) q

  ↭-drop-∷ : ∀ {x xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
  ↭-drop-∷ = ↭-dropMiddleElement [] []

--------------------------------------------------------------------------------
-- Quotient of lists up to permutation

_∣↭∣_ : {A : Type ℓ} → List A → List A → Type ℓ
xs ∣↭∣ ys = ∥ xs ↭ ys ∥₁

isPropValued∣↭∣ : isPropValued (_∣↭∣_ {A = A})
isPropValued∣↭∣ _ _ = squash₁

isEquivRel∣↭∣ : isEquivRel (_∣↭∣_ {A = A})
isEquivRel∣↭∣ .isEquivRel.reflexive x = ∣ ↭-refl ∣₁
isEquivRel∣↭∣ .isEquivRel.symmetric _ _ = PT.map ↭-sym
isEquivRel∣↭∣ .isEquivRel.transitive _ _ _ = PT.map2 ↭-trans

List↭ : Type ℓ → Type ℓ
List↭ A = List A / _∣↭∣_

pattern []↭ = [ [] ]

_ : List↭ A
_ = []↭

_∷↭_ : A → List↭ A → List↭ A
_∷↭_ x =
  SQ.rec
    squash/
    (λ xs → [ x ∷ xs ])
    (λ _ _ → eq/ _ _ ∘ PT.map (refl ↭-∷_))

comm↭ : (x y : A) (xs : List↭ A) → x ∷↭ y ∷↭ xs ≡ y ∷↭ x ∷↭ xs
comm↭ x y =
  SQ.elimProp
    (λ _ → squash/ _ _)
    (λ _ → eq/ _ _ ∣ ↭-comm refl refl ↭-refl ∣₁)

reify↭ : {xs ys : List A} → [ xs ] ≡ [ ys ] → xs ∣↭∣ ys
reify↭ = SQ.effective (λ _ _ → squash₁) isEquivRel∣↭∣ _ _

drop-∷↭ : (x : A) (xs ys : List↭ A) → x ∷↭ xs ≡ x ∷↭ ys → xs ≡ ys
drop-∷↭ x =
  SQ.elimProp2
    (λ _ _ → isProp→ (squash/ _ _))
    (λ _ _ → PT.rec (squash/ _ _) (eq/ _ _ ∘ ∣_∣₁ ∘ ↭-drop-∷) ∘ reify↭)

--------------------------------------------------------------------------------
-- FMSet A ≃ List↭ A

FMSet→List↭ : FMSet A → List↭ A
FMSet→List↭ = FMSet.Rec.f squash/ []↭ _∷↭_ comm↭

List→FMSet : List A → FMSet A
List→FMSet = List.foldr _∷_ []

perm→FMSetPath' : {xs ys : List A} → xs ↭ ys → List→FMSet xs ≡ List→FMSet ys
perm→FMSetPath' (↭-trans p q) = perm→FMSetPath' p ∙ perm→FMSetPath' q
perm→FMSetPath' {xs = []} {ys = []} ↭-[] = refl
perm→FMSetPath' {xs = x ∷ xs} {ys = y ∷ ys} (p ↭-∷ q) =
  cong₂ _∷_ p (perm→FMSetPath' q)
perm→FMSetPath' {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (↭-comm p q r) =
  comm x x' (List→FMSet xs)
    ∙ cong₃ (λ z w zs → z ∷ w ∷ zs) q p (perm→FMSetPath' r)

perm→FMSetPath : {xs ys : List A} → xs ∣↭∣ ys → List→FMSet xs ≡ List→FMSet ys
perm→FMSetPath = PT.rec (trunc _ _) perm→FMSetPath'

List↭→FMSet : List↭ A → FMSet A
List↭→FMSet = SQ.rec trunc List→FMSet (λ _ _ → perm→FMSetPath)

section' : (xs : List A) → FMSet→List↭ (List→FMSet xs) ≡ [ xs ]
section' [] = refl
section' (x ∷ xs) = cong (x ∷↭_) (section' xs)

section : (xs : List↭ A) → FMSet→List↭ (List↭→FMSet xs) ≡ xs
section = SQ.elimProp (λ _ → squash/ _ _) section'

List↭→FMSet-cons : (x : A) (xs : List↭ A) →
  List↭→FMSet (x ∷↭ xs) ≡ x ∷ List↭→FMSet xs
List↭→FMSet-cons x = SQ.elimProp (λ _ → trunc _ _) (λ _ → refl)

retract : (xs : FMSet A) → List↭→FMSet (FMSet→List↭ xs) ≡ xs
retract =
  FMSet.ElimProp.f (trunc _ _) refl λ x {xs} ih →
    List↭→FMSet-cons x (FMSet→List↭ xs) ∙ cong (x ∷_) ih

FMSetIsoList↭ : (A : Type ℓ) → Iso (FMSet A) (List↭ A)
FMSetIsoList↭ _ = iso FMSet→List↭ List↭→FMSet section retract

FMSet≡List↭ : (A : Type ℓ) → FMSet A ≡ List↭ A
FMSet≡List↭ A = isoToPath (FMSetIsoList↭ A)

--------------------------------------------------------------------------------
-- Time to reap the rewards!

consPath : PathP (λ i → A → FMSet≡List↭ A i → FMSet≡List↭ A i) _∷_ _∷↭_
consPath {A = A} = funExt λ x → toPathP (funExt λ xs →
    transport (λ i → FMSet≡List↭ A i → FMSet≡List↭ A i) (x ∷_) xs
  ≡⟨⟩
    transport (FMSet≡List↭ A) (x ∷ transport (sym (FMSet≡List↭ A)) xs)
  ≡⟨ transportIsoToPath (FMSetIsoList↭ A) (x ∷ transport (sym (FMSet≡List↭ A)) xs) ⟩
    FMSet→List↭ (x ∷ transport (sym (FMSet≡List↭ A)) xs)
  ≡⟨ cong (FMSet→List↭ ∘ (x ∷_)) (transportIsoToPath⁻ (FMSetIsoList↭ A) xs) ⟩
    FMSet→List↭ (x ∷ List↭→FMSet xs)
  ≡⟨⟩
    x ∷↭ FMSet→List↭ (List↭→FMSet xs)
  ≡⟨ cong (x ∷↭_) (section xs) ⟩
    x ∷↭ xs
  ∎)

drop-∷ : (x : A) (xs ys : FMSet A) → x ∷ xs ≡ x ∷ ys → xs ≡ ys
drop-∷ {A = A} =
  transport
    (λ i →
      (x : A) (xs ys : FMSet≡List↭ A (~ i)) →
      consPath (~ i) x xs ≡ consPath (~ i) x ys →
      xs ≡ ys)
    drop-∷↭
