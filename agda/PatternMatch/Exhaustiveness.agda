{-# OPTIONS --guardedness #-}

module PatternMatch.Exhaustiveness where

open import Data.Empty using ( ⊥-elim )
open import Data.Fin using ( Fin; zero; suc; _≟_ )
open import Data.List as List using ( List; _∷_; []; _++_; zipWith )
open import Data.List.Relation.Unary.Any using ( Any; any?; here; there )
open import Data.List.Relation.Unary.All as All using ( All; _∷_; [] )
open import Data.List.Relation.Unary.All.Properties using ( ++⁺; ++⁻ˡ; ++⁻ʳ; All¬⇒¬Any; ¬Any⇒All¬ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Vec.Relation.Unary.All using ( _∷_; [] )
open import Function using ( _∘_; const )
open import Relation.Nullary renaming ( map′ to mapDec )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import PatternMatch.Pattern
open import PatternMatch.PatternMatch

private
  variable
    A B : Set
    α β : Ty
    αs βs γs : List Ty

--------------------------------------------------------------------------------
-- Misc.

—* : Pat* αs
—* {[]} = []
—* {α ∷ αs} = — ∷ —* {αs}

—*≼ : (vs : Val* αs) → —* ≼* vs
—*≼ [] = []
—*≼ (v ∷ vs) = —≼ v ∷ —*≼ vs

cons* : List (Pat α) → List (Pat* αs) → List (Pat* (α ∷ αs))
cons* = zipWith _∷_

head* : List (Pat* (α ∷ αs)) → List (Pat α)
head* = List.map λ { (p ∷ _) → p }

tail* : List (Pat* (α ∷ αs)) → List (Pat* αs)
tail* = List.map λ { (_ ∷ ps) → ps }

--------------------------------------------------------------------------------

infixr 4 _,_

record Useful (p : Pat α) (ps : List (Pat α)) : Set where
  constructor _,_
  field
    {v} : Val α
    ev₁ : p ≼ v
    ev₂ : All (λ p → ¬ p ≼ v) ps

record Useful* (ps : Pat* αs) (pss : List (Pat* αs)) : Set where
  constructor _,_
  field
    {vs} : Val* αs
    ev₁ : ps ≼* vs
    ev₂ : All (λ ps → ¬ ps ≼* vs) pss

useful*-⊎ : ∀ {p : Pat α} {ps : Pat* αs} {pss}
  → Useful* (p ∷ ps) pss
  → Useful p (head* pss) ⊎ Useful* ps (tail* pss)
useful*-⊎ (_,_ {v ∷ vs} ev₁ ev₂) = {!   !}

useful*-⊎⁻ : ∀ {p : Pat α} {ps : Pat* αs} {pss}
  → Useful p (head* pss) ⊎ Useful* ps (tail* pss)
  → Useful* (p ∷ ps) pss
useful*-⊎⁻ {ps = ps} (inj₁ (ev₁ , ev₂)) =
  ev₁ ∷ ≼*-synth* ps , {!   !}
useful*-⊎⁻ {p = p} (inj₂ (ev₁ , ev₂)) =
  ≼-synth p ∷ ev₁ , {!   !}

specialize : (c : Con α) → List (Pat α) → List (Pat* (args α c))
specialize c [] = []
specialize c (— ∷ ps) = —* ∷ specialize c ps
specialize c (con c' ps ∷ qs) with c ≟ c'
... | yes refl = ps ∷ specialize c qs
... | no _ = specialize c qs
specialize c ((p ∣ q) ∷ ps) = specialize c (p ∷ ps) ++ specialize c (q ∷ ps)

specialize-con : ∀ {c : Con α} {ps : List (Pat α)} {vs}
  → All (λ ps → ¬ ps ≼* vs) (specialize c ps)
  → All (λ p → ¬ p ≼ con c vs) ps
specialize-con {ps = []} [] = []
specialize-con {ps = — ∷ ps} (h ∷ hs) =
  (λ { (—≼ con _ vs) → h (—*≼ vs) }) ∷ specialize-con hs
specialize-con {c = c} {con c' ps ∷ qs} hs with c ≟ c'
specialize-con {c = c} {con c ps ∷ qs} (h ∷ hs) | yes refl =
  (λ { (con .c h') → h h' }) ∷ specialize-con hs
specialize-con {c = c} {con c' ps ∷ qs} hs | no ¬c≡c' =
  (λ { (con .c _) → ¬c≡c' refl }) ∷ specialize-con hs
specialize-con {α} {c = c} {ps = (p ∣ q) ∷ qs} {vs} hs
  with h1 ∷ hs' ← specialize-con {ps = p ∷ qs} (++⁻ˡ (specialize c (p ∷ qs)) hs)
     | h2 ∷ _ ← specialize-con {ps = q ∷ qs} (++⁻ʳ (specialize c (p ∷ qs)) hs) =
    (λ { (h ∣-) → h1 h; (-∣ h) → h2 h }) ∷ hs'

useful-specialize-con : {c : Con α} {ps : Pat* (args α c)} {qs : List (Pat α)}
  → Useful* ps (specialize c qs)
  → Useful (con c ps) qs
useful-specialize-con {ps = ps} (ev₁ , ev₂) =
  con _ ev₁ , specialize-con ev₂

con-specialize : ∀ {c : Con α} {ps : List (Pat α)} {vs}
  → All (λ p → ¬ p ≼ con c vs) ps
  → All (λ ps → ¬ ps ≼* vs) (specialize c ps)
con-specialize {ps = []} [] = []
con-specialize {ps = — ∷ ps} {vs} (h ∷ hs) =
  const (h (—≼ con _ vs)) ∷ con-specialize hs
con-specialize {c = c} {con c' ps ∷ qs} (h ∷ hs) with c ≟ c'
... | yes refl = (h ∘ con _) ∷ con-specialize hs
... | no _ = con-specialize hs
con-specialize {ps = (p ∣ q) ∷ ps} (h ∷ hs) =
  ++⁺
    (con-specialize (h ∘ _∣- ∷ hs))
    (con-specialize (h ∘ -∣_ ∷ hs))

useful-con-specialize : {c : Con α} {ps : Pat* (args α c)} {qs : List (Pat α)}
  → Useful (con c ps) qs
  → Useful* ps (specialize c qs)
useful-con-specialize (con _ ev₁ , ev₂) =
  ev₁ , con-specialize ev₂

useful-∣-⊎ : ∀ {p q : Pat α} {ps}
  → Useful (p ∣ q) ps
  → Useful p ps ⊎ Useful q ps
useful-∣-⊎ (ev₁ ∣- , ev₂) = inj₁ (ev₁ , ev₂)
useful-∣-⊎ (-∣ ev₁ , ev₂) = inj₂ (ev₁ , ev₂)

useful-⊎-∣ : ∀ {p q : Pat α} {ps}
  → Useful p ps ⊎ Useful q ps
  → Useful (p ∣ q) ps
useful-⊎-∣ (inj₁ (ev₁ , ev₂)) = ev₁ ∣- , ev₂
useful-⊎-∣ (inj₂ (ev₁ , ev₂)) = -∣ ev₁ , ev₂

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

  useful*? : (ps : Pat* αs) (pss : List (Pat* αs)) → Dec (Useful* ps pss)
  useful*? [] [] = yes ([] , [])
  useful*? [] ([] ∷ pss) = no λ { ([] , ¬[]≼[] ∷ _) → ¬[]≼[] [] }
  useful*? (p ∷ ps) pss =
    mapDec
      useful*-⊎⁻
      useful*-⊎
      (useful? p (head* pss) ⊎-dec useful*? ps (tail* pss))

-- default : PatMat (α ∷ αs) → PatMat αs
-- default [] = []
-- default ((— ∷ ps) ∷ pss) = ps ∷ default pss
-- default ((con c ps ∷ qs) ∷ pss) = default pss
-- default (((p ∣ q) ∷ ps) ∷ pss) =
--   default ((p ∷ ps) ∷ pss) ++ default ((q ∷ ps) ∷ pss)

-- complete? : (pss : PatMat (α ∷ αs))
--   → Dec (⊤ ⊆ ⋃ (List.map pat-allCon (first-col pss)))
-- complete? {α} pss = ⊤ ⊆? ⋃ (List.map pat-allCon (first-col pss))

-- useful-—-default : ∀ {α} {ps : Pat* αs} {pss : PatMat (α ∷ αs)}
--   → (— ∷ ps) Useful pss
--   → ps Useful default pss
-- useful-—-default (- ∷ ps≼vs , ¬pss≼v∷vs) = ps≼vs , lemma12 ¬pss≼v∷vs

-- useful-default-— : ∀ {α αs} {ps : Pat* αs} {pss : PatMat (α ∷ αs)}
--   → ps Useful default pss
--   → (— ∷ ps) Useful pss
-- useful-default-— {α} (ps≼vs , ¬pss≼vs) = —≼ {!   !} ∷ ps≼vs , {!   !}

-- useful?-aux : (ps : Pat* αs) (pss : PatMat αs) → Acc ps → Dec (ps Useful pss)
-- useful?-aux [] [] acc = yes ([] , λ ())
-- useful?-aux [] ([] ∷ pss) acc = no λ { ([] , ¬pss≼[]) → ¬pss≼[] (success []) }
-- useful?-aux (_∷_ {α} — ps) pss (step-— acc acc') with complete? pss
-- ... | yes _ =
--       mapDec
--         {!   !}
--         {!   !}
--         (all′? (λ c → useful?-aux (++⁺ —* ps) (specialize c pss) acc) (allCon α))
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

-- _useful?_ : (ps : Pat* αs) (pss : PatMat αs) → Dec (ps Useful pss)
-- ps useful? pss = useful?-aux ps pss (∀Acc ps)

--------------------------------------------------------------------------------

Exhaustive : List (Pat α) → Set
Exhaustive ps = ∀ v → Any (_≼ v) ps

Exhaustive′ : List (Pat α) → Set
Exhaustive′ ps = ¬ Useful — ps

Exhaustive′→Exhaustive : {ps : List (Pat α)} → Exhaustive′ ps → Exhaustive ps
Exhaustive′→Exhaustive {ps = ps} ex v with match? v ps
... | yes ps≼v = ps≼v
... | no ¬ps≼v = ⊥-elim (ex (—≼ v , ¬Any⇒All¬ _ ¬ps≼v))

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
