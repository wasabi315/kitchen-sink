{-# OPTIONS --guardedness #-}

module PatternMatch.Exhaustiveness where

open import Data.Bool using ( T; _∧_; _∨_; not )
open import Data.Empty using ( ⊥-elim )
open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.List as List using ( List; _∷_; []; _++_; null; zipWith )
open import Data.List.Relation.Unary.Any using ( Any; any?; here; there )
open import Data.List.Relation.Unary.All as All using ( All; all?; _∷_; [] )
open import Data.List.Relation.Unary.All.Properties using ( ++⁺; ++⁻ˡ; ++⁻ʳ; All¬⇒¬Any; ¬Any⇒All¬; zipWith⁺ )
open import Data.Nat using ( ℕ; zero; suc; _≡ᵇ_; NonZero; _⊔_; _≤_ )
open import Data.Product using ( Σ-syntax; _×_; _,_; uncurry )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit using ( ⊤; tt )
open import Data.Vec as Vec using ( Vec; _∷_; []; allFin )
open import Data.Vec.Relation.Unary.All using ( _∷_; [] ) renaming ( all? to all′? )
open import Function using ( _∘_ )
open import Relation.Nullary renaming ( map′ to mapDec )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong )

open import PatternMatch.Utils
open import PatternMatch.Syntax
open import PatternMatch.PatternMatch

private
  variable
    A B : Set
    α β : Ty
    αs βs γs : List Ty

--------------------------------------------------------------------------------

—* : Pats αs
—* {[]} = []
—* {α ∷ αs} = — ∷ —* {αs}

cons* : List (Pat α) → List (Pats αs) → List (Pats (α ∷ αs))
cons* = zipWith _∷_

uncons* : (pss : List (Pats (α ∷ αs)))
  → Σ[ qs ∈ List (Pat α) ]
    Σ[ qss ∈ List (Pats αs) ]
    cons* qs qss ≡ pss
uncons* [] = [] , [] , refl
uncons* ((p ∷ ps) ∷ pss) =
  let qs , qss , h = uncons* pss
   in p ∷ qs , ps ∷ qss , cong ((p ∷ ps) ∷_) h

foo : ∀ {c : Ctor α} {vs : Vals (args α c)}
  → —* ≼* vs
  → — ≼ con {α} c vs
foo h = —≼ con _ {!  !}

bar : ∀ {c : Ctor α} {vs : Vals (args α c)}
  → — ≼ con {α} c vs
  → —* ≼* vs
bar (—≼ .(con _ _)) = {!   !}

--------------------------------------------------------------------------------

infixr 4 _,_

record Useful (p : Pat α) (ps : List (Pat α)) : Set where
  constructor _,_
  field
    {v} : Val α
    ev₁ : p ≼ v
    ev₂ : All (λ p → ¬ p ≼ v) ps

record Useful* (ps : Pats αs) (pss : List (Pats αs)) : Set where
  constructor _,_
  field
    {vs} : Vals αs
    ev₁ : ps ≼* vs
    ev₂ : All (λ ps → ¬ ps ≼* vs) pss

consUseful : ∀ {p : Pat α} {ps : Pats αs} {qs qss}
  → Useful p qs
  → Useful* ps qss
  → Useful* (p ∷ ps) (cons* qs qss)
consUseful (ev₁ , ev₂) (ev₁' , ev₂') = ev₁ ∷ ev₁' , zipWith⁺ _∷_ {!   !}

unconsUseful : ∀ {p : Pat α} {ps : Pats αs} {qs qss}
  → Useful* (p ∷ ps) (cons* qs qss)
  → Useful p qs × Useful* ps qss
unconsUseful ((ev₁ ∷ ev₁') , ev₂) = (ev₁ , {!   !}) , (ev₁' , {!   !})

specialize : (c : Ctor α) → List (Pat α) → List (Pats (args α c))
specialize c [] = []
specialize c (— ∷ ps) = —* ∷ specialize c ps
specialize c (con c' ps ∷ qs) with c ≟ c'
... | yes refl = ps ∷ specialize c qs
... | no _ = specialize c qs
specialize c ((p ∣ q) ∷ ps) = specialize c (p ∷ ps) ++ specialize c (q ∷ ps)

useful-specialize-con-aux : ∀ {c : Ctor α} {ps : List (Pat α)} {vs}
  → All (λ ps → ¬ ps ≼* vs) (specialize c ps)
  → All (λ p → ¬ p ≼ con c vs) ps
useful-specialize-con-aux {ps = []} [] = []
useful-specialize-con-aux {ps = — ∷ ps} (h ∷ hs) =
  (λ { (—≼ con _ vs) → h {!   !} }) ∷ useful-specialize-con-aux hs
useful-specialize-con-aux {c = c} {con c' ps ∷ qs} hs with c ≟ c'
useful-specialize-con-aux {c = c} {con c ps ∷ qs} (h ∷ hs) | yes refl =
  (λ { (con .c h') → h h' }) ∷ useful-specialize-con-aux hs
useful-specialize-con-aux {c = c} {con c' ps ∷ qs} hs | no ¬c≡c' =
  (λ { (con .c' _) → ¬c≡c' refl }) ∷ useful-specialize-con-aux hs
useful-specialize-con-aux {α} {c = c} {ps = (p ∣ q) ∷ qs} {vs} hs = {!   !}

useful-specialize-con : {c : Ctor α} {ps : Pats (args α c)} {qs : List (Pat α)}
  → Useful* ps (specialize c qs)
  → Useful (con c ps) qs
useful-specialize-con {ps = ps} (ev₁ , ev₂) =
  con _ ev₁ , useful-specialize-con-aux ev₂

useful-con-specialize-aux : ∀ {c : Ctor α} {ps : List (Pat α)} {vs}
  → All (λ p → ¬ p ≼ con c vs) ps
  → All (λ ps → ¬ ps ≼* vs) (specialize c ps)
useful-con-specialize-aux {ps = []} [] = []
useful-con-specialize-aux {ps = — ∷ ps} (h ∷ hs) =
  h ∘ foo ∷ useful-con-specialize-aux hs
useful-con-specialize-aux {c = c} {con c' ps ∷ qs} (h ∷ hs) with c ≟ c'
... | yes refl = (h ∘ con _) ∷ useful-con-specialize-aux hs
... | no _ = useful-con-specialize-aux hs
useful-con-specialize-aux {ps = (p ∣ q) ∷ ps} (h ∷ hs) =
  ++⁺
    (useful-con-specialize-aux (h ∘ ∣₁ ∷ hs))
    (useful-con-specialize-aux (h ∘ ∣₂ ∷ hs))

useful-con-specialize : {c : Ctor α} {ps : Pats (args α c)} {qs : List (Pat α)}
  → Useful (con c ps) qs
  → Useful* ps (specialize c qs)
useful-con-specialize (con _ ev₁ , ev₂) =
  ev₁ , useful-con-specialize-aux ev₂

useful-∣-⊎ : ∀ {p q : Pat α} {ps}
  → Useful (p ∣ q) ps
  → Useful p ps ⊎ Useful q ps
useful-∣-⊎ (∣₁ ev₁ , ev₂) = inj₁ (ev₁ , ev₂)
useful-∣-⊎ (∣₂ ev₁ , ev₂) = inj₂ (ev₁ , ev₂)

useful-⊎-∣ : ∀ {p q : Pat α} {ps}
  → Useful p ps ⊎ Useful q ps
  → Useful (p ∣ q) ps
useful-⊎-∣ (inj₁ (ev₁ , ev₂)) = ∣₁ ev₁ , ev₂
useful-⊎-∣ (inj₂ (ev₁ , ev₂)) = ∣₂ ev₁ , ev₂

mutual

  useful? : (p : Pat α) (ps : List (Pat α)) → Dec (Useful p ps)
  useful? — ps = {!   !}
  useful? (con c ps) qs =
    mapDec
      useful-specialize-con
      useful-con-specialize
      (useful*? ps (specialize c qs))
  useful? (p ∣ q) ps =
    mapDec
      useful-⊎-∣
      useful-∣-⊎
      (useful? p ps ⊎-dec useful? q ps)

  useful*? : (ps : Pats αs) (pss : List (Pats αs)) → Dec (Useful* ps pss)
  useful*? [] [] = yes ([] , [])
  useful*? [] ([] ∷ pss) = no λ { ([] , ¬[]≼[] ∷ _) → ¬[]≼[] [] }
  useful*? (p ∷ ps) pss with uncons* pss
  ... | qs , qss , refl =
        mapDec
          (uncurry consUseful)
          unconsUseful
          (useful? p qs ×-dec useful*? ps qss)

-- default : PatMat (α ∷ αs) → PatMat αs
-- default [] = []
-- default ((— ∷ ps) ∷ pss) = ps ∷ default pss
-- default ((con c ps ∷ qs) ∷ pss) = default pss
-- default (((p ∣ q) ∷ ps) ∷ pss) =
--   default ((p ∷ ps) ∷ pss) ++ default ((q ∷ ps) ∷ pss)

-- complete? : (pss : PatMat (α ∷ αs))
--   → Dec (⊤ ⊆ ⋃ (List.map pat-ctors (first-col pss)))
-- complete? {α} pss = ⊤ ⊆? ⋃ (List.map pat-ctors (first-col pss))

-- useful-—-default : ∀ {α} {ps : Pats αs} {pss : PatMat (α ∷ αs)}
--   → (— ∷ ps) Useful pss
--   → ps Useful default pss
-- useful-—-default (- ∷ ps≼vs , ¬pss≼v∷vs) = ps≼vs , lemma12 ¬pss≼v∷vs

-- useful-default-— : ∀ {α αs} {ps : Pats αs} {pss : PatMat (α ∷ αs)}
--   → ps Useful default pss
--   → (— ∷ ps) Useful pss
-- useful-default-— {α} (ps≼vs , ¬pss≼vs) = —≼ {!   !} ∷ ps≼vs , {!   !}

-- useful?-aux : (ps : Pats αs) (pss : PatMat αs) → Acc ps → Dec (ps Useful pss)
-- useful?-aux [] [] acc = yes ([] , λ ())
-- useful?-aux [] ([] ∷ pss) acc = no λ { ([] , ¬pss≼[]) → ¬pss≼[] (success []) }
-- useful?-aux (_∷_ {α} — ps) pss (step-— acc acc') with complete? pss
-- ... | yes _ =
--       mapDec
--         {!   !}
--         {!   !}
--         (all′? (λ c → useful?-aux (++⁺ —* ps) (specialize c pss) acc) (ctors α))
-- ... | no _ =
--       mapDec
--         -- useful-default-—
--         {!   !}
--         useful-—-default
--         (useful?-aux ps (default pss) acc')
-- useful?-aux (con c ps ∷ qs) pss (step-con acc) =
--   mapDec
--     useful-specialize-con
--     useful-con-specialize
--     (useful?-aux (++⁺ ps qs) (specialize c pss) acc)
-- useful?-aux ((p ∣ q) ∷ ps) pss (step-∣ acc acc') =
--   mapDec
--     useful-⊎-∣
--     useful-∣-⊎
--     (useful?-aux (p ∷ ps) pss acc ⊎-dec useful?-aux (q ∷ ps) pss acc')

-- _useful?_ : (ps : Pats αs) (pss : PatMat αs) → Dec (ps Useful pss)
-- ps useful? pss = useful?-aux ps pss (∀Acc ps)

--------------------------------------------------------------------------------

Exhaustive : List (Pat α) → Set
Exhaustive ps = ∀ v → Any (_≼ v) ps

Exhaustive′ : List (Pat α) → Set
Exhaustive′ ps = ¬ Useful — ps

Exhaustive′→Exhaustive : {ps : List (Pat α)} → Exhaustive′ ps → Exhaustive ps
Exhaustive′→Exhaustive ex v = {!   !}

Exhaustive→Exhaustive′ : {ps : List (Pat α)} → Exhaustive ps → Exhaustive′ ps
Exhaustive→Exhaustive′ ex (_,_ {v} ev₁ ev₂) = All¬⇒¬Any ev₂ (ex v)

exhaustive′? : (ps : List (Pat α)) → Dec (Exhaustive′ ps)
exhaustive′? ps = ¬? (useful? — ps)

exhaustive? : (ps : List (Pat α)) → Dec (Exhaustive ps)
exhaustive? ps =
  mapDec
    Exhaustive′→Exhaustive
    Exhaustive→Exhaustive′
    (exhaustive′? ps)
