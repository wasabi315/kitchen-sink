open import Level using ( Level; Lift; lower; lift; 0ℓ ) renaming ( suc to sucℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.List using ( List; []; _∷_ )
open import Data.Maybe using ( Maybe; nothing; just )
open import Data.Nat using ( ℕ )
open import Data.Product as Prod using ( _×_; _,_; proj₁; proj₂ )
open import Data.Product.Algebra using ( ×-identityˡ; ×-zeroˡ; ×-cong; ×-assoc; ×-comm; ×-distribʳ-⊎ )
open import Data.Sum as Sum using ( _⊎_; inj₁; inj₂; [_,_] )
open import Data.Sum.Algebra using ( ⊎-cong )
open import Data.Unit using ( ⊤; tt )
open import Function using ( case_of_; id; Inverse; _↔_; mk↔ₛ′ )
open import Function.Properties.Inverse using ( ↔-refl; ↔-sym; ↔-trans; ↔-isEquivalence )
open import Relation.Binary.Bundles using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )
open import Relation.Nullary using ( Dec; yes; no )

open Inverse

private
  variable
    ℓ ℓ' : Level
    A B C D J : Set

--------------------------------------------------------------------------------

↔-setoid : ∀ ℓ → Setoid (sucℓ ℓ) ℓ
↔-setoid ℓ = record { isEquivalence = ↔-isEquivalence {ℓ = ℓ} }

module ↔-Reasoning {ℓ} where
  open import Relation.Binary.Reasoning.Setoid (↔-setoid ℓ) public

lift↔ : {A : Set ℓ} → Lift 0ℓ A ↔ A
lift↔ = mk↔ₛ′ lower lift (λ _ → refl) (λ _ → refl)

×-zeroˡ′ : (A : Set) → (⊥ × A) ↔ ⊥
×-zeroˡ′ A = ↔-trans (×-cong (↔-sym lift↔) ↔-refl) (↔-trans (×-zeroˡ _ A) lift↔)

×-identityˡ′ : (A : Set) → (⊤ × A) ↔ A
×-identityˡ′ A = ↔-trans (×-cong (↔-sym lift↔) ↔-refl) (×-identityˡ _ _)

--------------------------------------------------------------------------------
-- Polynomial (bi)functors

infix 30 _×̂_
infix 20 _+̂_

data Poly : Set₁ where
  Const : (A : Set) → Poly
  Id : Poly
  _+̂_ : (F G : Poly) → Poly
  _×̂_ : (F G : Poly) → Poly

data BiPoly : Set₁ where
  Const : (A : Set) → BiPoly
  Fst : BiPoly
  Snd : BiPoly
  _+̂_ : (F G : BiPoly) → BiPoly
  _×̂_ : (F G : BiPoly) → BiPoly

⟦_⟧₁ : Poly → (Set → Set)
⟦ Const A ⟧₁ X = A
⟦ Id ⟧₁ X = X
⟦ F +̂ G ⟧₁ X = ⟦ F ⟧₁ X ⊎ ⟦ G ⟧₁ X
⟦ F ×̂ G ⟧₁ X = ⟦ F ⟧₁ X × ⟦ G ⟧₁ X

⟦_⟧₂ : BiPoly → (Set → Set → Set)
⟦ Const A ⟧₂ X Y = A
⟦ Fst ⟧₂ X Y = X
⟦ Snd ⟧₂ X Y = Y
⟦ F +̂ G ⟧₂ X Y = ⟦ F ⟧₂ X Y ⊎ ⟦ G ⟧₂ X Y
⟦ F ×̂ G ⟧₂ X Y = ⟦ F ⟧₂ X Y × ⟦ G ⟧₂ X Y

map : ∀ F → (A → B) → ⟦ F ⟧₁ A → ⟦ F ⟧₁ B
map (Const A) f x = x
map Id f x = f x
map (F +̂ G) f = Sum.map (map F f) (map G f)
map (F ×̂ G) f = Prod.map (map F f) (map G f)

bimap : ∀ F → (A → B) → (C → D) → ⟦ F ⟧₂ A C → ⟦ F ⟧₂ B D
bimap (Const A) f g x = x
bimap Fst f g x = f x
bimap Snd f g x = g x
bimap (F +̂ G) f g = Sum.map (bimap F f g) (bimap G f g)
bimap (F ×̂ G) f g = Prod.map (bimap F f g) (bimap G f g)

--------------------------------------------------------------------------------

data μ (F : Poly) : Set where
  sup : ⟦ F ⟧₁ (μ F) → μ F

mapFold : ∀ F G → (⟦ G ⟧₁ A → A) → ⟦ F ⟧₁ (μ G) → ⟦ F ⟧₁ A
mapFold (Const A) G alg x = x
mapFold Id G alg (sup x) = alg (mapFold G G alg x)
mapFold (F +̂ G) H alg (inj₁ x) = inj₁ (mapFold F H alg x)
mapFold (F +̂ G) H alg (inj₂ x) = inj₂ (mapFold G H alg x)
mapFold (F ×̂ G) H alg (x , y) = mapFold F H alg x , mapFold G H alg y

fold : ∀ F → (⟦ F ⟧₁ A → A) → μ F → A
fold F alg (sup x) = alg (mapFold F F alg x)

--------------------------------------------------------------------------------

-- clown
◿ : Poly → BiPoly
◿ (Const A) = Const A
◿ Id = Fst
◿ (F +̂ G) = ◿ F +̂ ◿ G
◿ (F ×̂ G) = ◿ F ×̂ ◿ G

-- joker
◺ : Poly → BiPoly
◺ (Const A) = Const A
◺ Id = Snd
◺ (F +̂ G) = ◺ F +̂ ◺ G
◺ (F ×̂ G) = ◺ F ×̂ ◺ G

clown↔ : ∀ F → ⟦ F ⟧₁ A ↔ ⟦ ◿ F ⟧₂ A B
clown↔ (Const A) = ↔-refl
clown↔ Id = ↔-refl
clown↔ (F +̂ G) = ⊎-cong (clown↔ F) (clown↔ G)
clown↔ (F ×̂ G) = ×-cong (clown↔ F) (clown↔ G)

joker↔ : ∀ {A B} F → ⟦ F ⟧₁ B ↔ ⟦ ◺ F ⟧₂ A B
joker↔ (Const A) = ↔-refl
joker↔ Id = ↔-refl
joker↔ (F +̂ G) = ⊎-cong (joker↔ F) (joker↔ G)
joker↔ (F ×̂ G) = ×-cong (joker↔ F) (joker↔ G)

--------------------------------------------------------------------------------

infixl 40 _∙_ _∙∙_

_∙_ : Poly → Poly → Poly
Const A ∙ G = Const A
Id ∙ G = G
(F +̂ G) ∙ H = F ∙ H +̂ G ∙ H
(F ×̂ G) ∙ H = F ∙ H ×̂ G ∙ H

comp↔ : ∀ F G → ⟦ F ⟧₁ (⟦ G ⟧₁ A) ↔ ⟦ F ∙ G ⟧₁ A
comp↔ (Const A) G = ↔-refl
comp↔ Id G = ↔-refl
comp↔ (F +̂ G) H = ⊎-cong (comp↔ F H) (comp↔ G H)
comp↔ (F ×̂ G) H = ×-cong (comp↔ F H) (comp↔ G H)

_∙∙_ : BiPoly → Poly → BiPoly
Const A ∙∙ G = Const A
Fst ∙∙ G = ◿ G
Snd ∙∙ G = ◺ G
(F +̂ G) ∙∙ H = F ∙∙ H +̂ G ∙∙ H
(F ×̂ G) ∙∙ H = F ∙∙ H ×̂ G ∙∙ H

comp2↔ : ∀ F G → ⟦ F ⟧₂ (⟦ G ⟧₁ A) (⟦ G ⟧₁ B) ↔ ⟦ F ∙∙ G ⟧₂ A B
comp2↔ (Const A) G = ↔-refl
comp2↔ Fst G = clown↔ G
comp2↔ Snd G = joker↔ G
comp2↔ (F +̂ G) H = ⊎-cong (comp2↔ F H) (comp2↔ G H)
comp2↔ (F ×̂ G) H = ×-cong (comp2↔ F H) (comp2↔ G H)

clown-comp : ∀ F G → ⟦ ◿ (F ∙ G) ⟧₂ C J ↔ ⟦ ◿ F ∙∙ G ⟧₂ C J
clown-comp {C} {J} F G = begin
  ⟦ ◿ (F ∙ G) ⟧₂ C J              ≈⟨ clown↔ (F ∙ G) ⟨
  ⟦ F ∙ G ⟧₁ C                    ≈⟨ comp↔ F G ⟨
  ⟦ F ⟧₁ (⟦ G ⟧₁ C)               ≈⟨ clown↔ F ⟩
  ⟦ ◿ F ⟧₂ (⟦ G ⟧₁ C) (⟦ G ⟧₁ J)  ≈⟨ comp2↔ (◿ F) G ⟩
  ⟦ ◿ F ∙∙ G ⟧₂ C J               ∎
  where open ↔-Reasoning

joker-comp : ∀ F G → ⟦ ◺ (F ∙ G) ⟧₂ C J ↔ ⟦ ◺ F ∙∙ G ⟧₂ C J
joker-comp {C} {J} F G = begin
  ⟦ ◺ (F ∙ G) ⟧₂ C J              ≈⟨ joker↔ (F ∙ G) ⟨
  ⟦ F ∙ G ⟧₁ J                    ≈⟨ comp↔ F G ⟨
  ⟦ F ⟧₁ (⟦ G ⟧₁ J)               ≈⟨ joker↔ F ⟩
  ⟦ ◺ F ⟧₂ (⟦ G ⟧₁ C) (⟦ G ⟧₁ J)  ≈⟨ comp2↔ (◺ F) G ⟩
  ⟦ ◺ F ∙∙ G ⟧₂ C J               ∎
  where open ↔-Reasoning

--------------------------------------------------------------------------------

-- From a polynomial functor to its dissection
Δ : Poly → BiPoly
Δ (Const A) = Const ⊥
Δ Id = Const ⊤
Δ (F +̂ G) = Δ F +̂ Δ G
Δ (F ×̂ G) = Δ F ×̂ ◺ G +̂ ◿ F ×̂ Δ G

module _ where
  open ↔-Reasoning

  chain-rule : ∀ F G → ⟦ Δ (F ∙ G) ⟧₂ C J ↔ ⟦ Δ F ∙∙ G ×̂ Δ G ⟧₂ C J
  chain-rule (Const A) G = ↔-sym (×-zeroˡ′ _)
  chain-rule Id G = ↔-sym (×-identityˡ′ _)
  chain-rule {C} {J} (F +̂ G) H =
    begin
      ⟦ Δ ((F +̂ G) ∙ H) ⟧₂ C J
    ≡⟨⟩
      (⟦ Δ (F ∙ H) ⟧₂ C J ⊎ ⟦ Δ (G ∙ H) ⟧₂ C J)
    ≈⟨ ⊎-cong (chain-rule F H) (chain-rule G H) ⟩
      (⟦ Δ F ∙∙ H ×̂ Δ H ⟧₂ C J ⊎ ⟦ Δ G ∙∙ H ×̂ Δ H ⟧₂ C J)
    ≡⟨⟩
      ((⟦ Δ F ∙∙ H ⟧₂ C J × ⟦ Δ H ⟧₂ C J) ⊎ (⟦ Δ G ∙∙ H ⟧₂ C J × ⟦ Δ H ⟧₂ C J))
    ≈⟨ ×-distribʳ-⊎ _ _ _ _ ⟨
      ((⟦ Δ F ∙∙ H ⟧₂ C J ⊎ ⟦ Δ G ∙∙ H ⟧₂ C J) × ⟦ Δ H ⟧₂ C J)
    ≡⟨⟩
      (⟦ Δ (F +̂ G) ∙∙ H ⟧₂ C J × ⟦ Δ H ⟧₂ C J)
    ∎
  chain-rule {C} {J} (F ×̂ G) H =
    begin
      ⟦ Δ ((F ×̂ G) ∙ H) ⟧₂ C J
    ≡⟨⟩
      (⟦ Δ (F ∙ H) ⟧₂ C J × ⟦ ◺ (G ∙ H) ⟧₂ C J ⊎
       ⟦ ◿ (F ∙ H) ⟧₂ C J × ⟦ Δ (G ∙ H) ⟧₂ C J)
    ≈⟨ ⊎-cong
        (×-cong (chain-rule F H) (joker-comp G H))
        (×-cong (clown-comp F H) (chain-rule G H)) ⟩
      ((⟦ Δ F ∙∙ H ⟧₂ C J × ⟦ Δ H ⟧₂ C J) × ⟦ ◺ G ∙∙ H ⟧₂ C J ⊎
       (⟦ ◿ F ∙∙ H ⟧₂ C J × (⟦ Δ G ∙∙ H ⟧₂ C J × ⟦ Δ H ⟧₂ C J)))
    ≈⟨ ⊎-cong
        (↔-trans (×-assoc _ _ _ _) (↔-trans (×-cong ↔-refl (×-comm _ _)) (↔-sym (×-assoc _ _ _ _))))
        (↔-sym (×-assoc _ _ _ _)) ⟩
      ((⟦ Δ F ∙∙ H ⟧₂ C J × ⟦ ◺ G ∙∙ H ⟧₂ C J) × ⟦ Δ H ⟧₂ C J ⊎
       ((⟦ ◿ F ∙∙ H ⟧₂ C J × ⟦ Δ G ∙∙ H ⟧₂ C J) × ⟦ Δ H ⟧₂ C J))
    ≈⟨ ×-distribʳ-⊎ _ _ _ _ ⟨
      ((⟦ Δ F ∙∙ H ⟧₂ C J × ⟦ ◺ G ∙∙ H ⟧₂ C J ⊎
        ⟦ ◿ F ∙∙ H ⟧₂ C J × ⟦ Δ G ∙∙ H ⟧₂ C J) × ⟦ Δ H ⟧₂ C J)
    ≡⟨⟩
      (⟦ Δ (F ×̂ G) ∙∙ H ⟧₂ C J × ⟦ Δ H ⟧₂ C J)
    ∎

--------------------------------------------------------------------------------

RightArg RightRet : Poly → Set → Set → Set
RightArg F C J = ⟦ F ⟧₁ J ⊎ ⟦ Δ F ⟧₂ C J × C
RightRet F C J = J × ⟦ Δ F ⟧₂ C J ⊎ ⟦ F ⟧₁ C

right : ∀ F → RightArg F C J → RightRet F C J
mindp : ∀ F G → RightRet F C J → ⟦ G ⟧₁ J → RightRet (F ×̂ G) C J
mindq : ∀ F G → ⟦ F ⟧₁ C → RightRet G C J → RightRet (F ×̂ G) C J

right (Const A) (inj₁ x) = inj₂ x
right Id (inj₁ x) = inj₁ (x , tt)
right Id (inj₂ (tt , x)) = inj₂ x
right (F +̂ G) (inj₁ (inj₁ fj)) = Sum.map (Prod.map₂ inj₁) inj₁ (right F (inj₁ fj))
right (F +̂ G) (inj₁ (inj₂ gj)) = Sum.map (Prod.map₂ inj₂) inj₂ (right G (inj₁ gj))
right (F +̂ G) (inj₂ (inj₁ fd , c)) = Sum.map (Prod.map₂ inj₁) inj₁ (right F (inj₂ (fd , c)))
right (F +̂ G) (inj₂ (inj₂ gd , c)) = Sum.map (Prod.map₂ inj₂) inj₂ (right G (inj₂ (gd , c)))
right (F ×̂ G) (inj₁ (fj , gj)) = mindp F G (right F (inj₁ fj)) gj
right (F ×̂ G) (inj₂ (inj₁ (fd , gj) , c)) = mindp F G (right F (inj₂ (fd , c))) (from (joker↔ G) gj)
right (F ×̂ G) (inj₂ (inj₂ (fc , gd) , c)) = mindq F G (from (clown↔ F) fc) (right G (inj₂ (gd , c)))

mindp F G (inj₁ (j , fd)) gj = inj₁ (j , inj₁ (fd , to (joker↔ G) gj))
mindp F G (inj₂ fc) gj = mindq F G fc (right G (inj₁ gj))

mindq F G fc (inj₁ (j , gd)) = inj₁ (j , inj₂ (to (clown↔ F) fc , gd))
mindq F G fc (inj₂ gc) = inj₂ (fc , gc)

plug : ∀ F → A → ⟦ Δ F ⟧₂ A A → ⟦ F ⟧₁ A
plug Id x tt = x
plug (F +̂ G) x (inj₁ fd) = inj₁ (plug F x fd)
plug (F +̂ G) x (inj₂ gd) = inj₂ (plug G x gd)
plug (F ×̂ G) x (inj₁ (fd , gx)) = plug F x fd , from (joker↔ G) gx
plug (F ×̂ G) x (inj₂ (fx , gd)) = from (clown↔ F) fx , plug G x gd

--------------------------------------------------------------------------------

Context : Poly → Set
Context F = μ F × List (⟦ Δ F ⟧₂ (μ F) (μ F))

zUp zDown zRight : ∀ F → Context F → Maybe (Context F)
zUp F (t , []) = nothing
zUp F (t , d ∷ ds) = just (sup (plug F t d) , ds)
zDown F (sup ft , ds) with right F (inj₁ ft)
... | inj₁ (t , d) = just (t , d ∷ ds)
... | inj₂ _ = nothing
zRight F (t , []) = nothing
zRight F (t , d ∷ ds) with right F (inj₂ (d , t))
... | inj₁ (t′ , d′) = just (t′ , d′ ∷ ds)
... | inj₂ _ = nothing

--------------------------------------------------------------------------------

Quot : Poly → Set → Set
Quot F A = ⟦ Δ F ⟧₂ ⊥ A

Rem : Poly → Set
Rem F = ⟦ F ⟧₁ ⊥

divide : ∀ F → ⟦ F ⟧₁ A → A × Quot F A ⊎ Rem F
divide F fx = right F (inj₁ fx)

divide⁻ : ∀ F → A × Quot F A ⊎ Rem F → ⟦ F ⟧₁ A
divide⁻ F (inj₁ (x , q)) = plug F x (bimap (Δ F) ⊥-elim id q)
divide⁻ F (inj₂ fz) = map F ⊥-elim fz

divide-divide⁻ : ∀ F (fx : ⟦ F ⟧₁ A) → divide⁻ F (divide F fx) ≡ fx
divide-divide⁻ (Const A) x = refl
divide-divide⁻ Id x = refl
divide-divide⁻ (F +̂ G) (inj₁ x) = {!   !}
divide-divide⁻ (F +̂ G) (inj₂ y) = {!   !}
divide-divide⁻ (F ×̂ G) x = {!   !}

divide⁻-divide : ∀ F (fx : A × ⟦ Δ F ⟧₂ ⊥ A ⊎ ⟦ F ⟧₁ ⊥) → divide F (divide⁻ F fx) ≡ fx
divide⁻-divide F x = {!   !}
