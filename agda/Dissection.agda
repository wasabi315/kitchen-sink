open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.List using ( List; []; _∷_ )
open import Data.Maybe using ( Maybe; nothing; just )
open import Data.Nat using ( ℕ )
open import Data.Product as Prod using ( _×_; _,_ )
open import Data.Sum as Sum using ( _⊎_; inj₁; inj₂; [_,_] )
open import Data.Unit using ( ⊤; tt )
open import Function using ( case_of_; id )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

private
  variable
    A B C D J : Set

--------------------------------------------------------------------------------
-- Polynomial (bi)functors

infix 40 ⌊_ ⌋_
infix 30 _×̂_
infix 20 _+̂_

data U₁ : Set₁ where
  Const : (A : Set) → U₁
  Id : U₁
  _+̂_ : U₁ → U₁ → U₁
  _×̂_ : U₁ → U₁ → U₁

data U₂ : Set₁ where
  Const : (A : Set) → U₂
  ⌊_ : U₁ → U₂ -- clown
  ⌋_ : U₁ → U₂ -- joker
  _+̂_ : U₂ → U₂ → U₂
  _×̂_ : U₂ → U₂ → U₂

pattern Fst = ⌊ Id
pattern Snd = ⌋ Id

⟦_⟧₁ : U₁ → (Set → Set)
⟦ Const A ⟧₁ _ = A
⟦ Id ⟧₁ X = X
⟦ u +̂ v ⟧₁ X = ⟦ u ⟧₁ X ⊎ ⟦ v ⟧₁ X
⟦ u ×̂ v ⟧₁ X = ⟦ u ⟧₁ X × ⟦ v ⟧₁ X

⟦_⟧₂ : U₂ → (Set → Set → Set)
⟦ Const A ⟧₂ X Y = A
⟦ ⌊ u ⟧₂ X Y = ⟦ u ⟧₁ X
⟦ ⌋ u ⟧₂ X Y = ⟦ u ⟧₁ Y
⟦ u +̂ v ⟧₂ X Y = ⟦ u ⟧₂ X Y ⊎ ⟦ v ⟧₂ X Y
⟦ u ×̂ v ⟧₂ X Y = ⟦ u ⟧₂ X Y × ⟦ v ⟧₂ X Y

map : ∀ {U} → (A → B) → ⟦ U ⟧₁ A → ⟦ U ⟧₁ B
map {U = Const A} f x = x
map {U = Id} f x = f x
map {U = U +̂ V} f = Sum.map (map {U = U} f) (map {U = V} f)
map {U = U ×̂ V} f = Prod.map (map {U = U} f) (map {U = V} f)

bimap : ∀ {U} → (A → B) → (C → D) → ⟦ U ⟧₂ A C → ⟦ U ⟧₂ B D
bimap {U = Const A} f g x = x
bimap {U = ⌊ U} f g x = map {U = U} f x
bimap {U = ⌋ U} f g x = map {U = U} g x
bimap {U = U +̂ V} f g = Sum.map (bimap {U = U} f g) (bimap {U = V} f g)
bimap {U = U ×̂ V} f g = Prod.map (bimap {U = U} f g) (bimap {U = V} f g)

data μ (U : U₁) : Set where
  sup : ⟦ U ⟧₁ (μ U) → μ U

--------------------------------------------------------------------------------

-- TODO: Dissection of the semantics of a container?

-- From a polynomial functor to its dissection
Δ : U₁ → U₂
Δ (Const A) = Const ⊥
Δ Id = Const ⊤
Δ (u +̂ v) = Δ u +̂ Δ v
Δ (u ×̂ v) = Δ u ×̂ ⌋ v +̂ ⌊ u ×̂ Δ v

RightArg RightRet : U₁ → Set → Set → Set
RightArg F C J = ⟦ F ⟧₁ J ⊎ ⟦ Δ F ⟧₂ C J × C
RightRet F C J = J × ⟦ Δ F ⟧₂ C J ⊎ ⟦ F ⟧₁ C

right : ∀ {F} → RightArg F C J → RightRet F C J
right {F = Const A} (inj₁ x) = inj₂ x
right {F = Id} (inj₁ x) = inj₁ (x , tt)
right {F = Id} (inj₂ (tt , x)) = inj₂ x
right {F = F +̂ G} x = case x of λ
  { (inj₁ (inj₁ fj)) → mindf (right {F = F} (inj₁ fj))
  ; (inj₁ (inj₂ gj)) → mindg (right {F = G} (inj₁ gj))
  ; (inj₂ (inj₁ fd , c)) → mindf (right {F = F} (inj₂ (fd , c)))
  ; (inj₂ (inj₂ gd , c)) → mindg (right {F = G} (inj₂ (gd , c)))
  }
  where
    mindf : RightRet F C J → RightRet (F +̂ G) C J
    mindg : RightRet G C J → RightRet (F +̂ G) C J
    mindf (inj₁ (j , fd)) = inj₁ (j , inj₁ fd)
    mindf (inj₂ fc) = inj₂ (inj₁ fc)
    mindg (inj₁ (j , gd)) = inj₁ (j , inj₂ gd)
    mindg (inj₂ qc) = inj₂ (inj₂ qc)
right {F = F ×̂ G} x = case x of λ
  { (inj₁ (fj , gj)) → mindf (right {F = F} (inj₁ fj)) gj
  ; (inj₂ (inj₁ (fd , gj) , c)) → mindf (right {F = F} (inj₂ (fd , c))) gj
  ; (inj₂ (inj₂ (fc , gd) , c)) → mindg fc (right {F = G} (inj₂ (gd , c)))
  }
  where
    mindf : RightRet F C J → ⟦ G ⟧₁ J → RightRet (F ×̂ G) C J
    mindg : ⟦ F ⟧₁ C → RightRet G C J → RightRet (F ×̂ G) C J
    mindf (inj₁ (j , fd)) gj = inj₁ (j , inj₁ (fd , gj))
    mindf (inj₂ fc) gj = mindg fc (right {F = G} (inj₁ gj))
    mindg fc (inj₁ (j , gd)) = inj₁ (j , inj₂ (fc , gd))
    mindg fc (inj₂ gc) = inj₂ (fc , gc)

plug : ∀ {F} → A → ⟦ Δ F ⟧₂ A A → ⟦ F ⟧₁ A
plug {F = Id} x tt = x
plug {F = F +̂ G} x (inj₁ fd) = inj₁ (plug {F = F} x fd)
plug {F = F +̂ G} x (inj₂ gd) = inj₂ (plug {F = G} x gd)
plug {F = F ×̂ G} x (inj₁ (fd , gx)) = plug {F = F} x fd , gx
plug {F = F ×̂ G} x (inj₂ (fx , gd)) = fx , plug {F = G} x gd

--------------------------------------------------------------------------------

zUp zDown zRight : ∀ {F}
  → μ F × List (⟦ Δ F ⟧₂ (μ F) (μ F))
  → Maybe (μ F × List (⟦ Δ F ⟧₂ (μ F) (μ F)))
zUp (t , []) = nothing
zUp {F = F} (t , d ∷ ds) = just (sup (plug {F = F} t d) , ds)
zDown {F = F} (sup ft , ds) = case right {F = F} (inj₁ ft) of λ
  { (inj₁ (t , d)) → just (t , d ∷ ds)
  ; (inj₂ _) → nothing
  }
zRight (t , []) = nothing
zRight {F = F} (t , d ∷ ds) = case right {F = F} (inj₂ (d , t)) of λ
  { (inj₁ (t′ , d′)) → just (t′ , d′ ∷ ds)
  ; (inj₂ _) → nothing
  }

--------------------------------------------------------------------------------

divide : ∀ {F} → ⟦ F ⟧₁ A → A × ⟦ Δ F ⟧₂ ⊥ A ⊎ ⟦ F ⟧₁ ⊥
divide {F = F} fx = right {F = F} (inj₁ fx)

unite : ∀ {F} → A × ⟦ Δ F ⟧₂ ⊥ A ⊎ ⟦ F ⟧₁ ⊥ → ⟦ F ⟧₁ A
unite {F = F} (inj₁ (x , q)) = plug {F = F} x (bimap {U = Δ F} ⊥-elim id q)
unite {F = F} (inj₂ fz) = map {U = F} ⊥-elim fz

divide-unite : ∀ {F} (fx : ⟦ F ⟧₁ A) → unite {F = F} (divide {F = F} fx) ≡ fx
divide-unite {F = Const A} x = refl
divide-unite {F = Id} x = refl
divide-unite {F = F +̂ G} (inj₁ x) with right {C = ⊥} {F = F} (inj₁ x)
... | inj₁ (j , d) = {!   !}
... | inj₂ y = {!   !}
divide-unite {F = F +̂ G} (inj₂ x) = {!   !}
divide-unite {F = F ×̂ G} (x , y) = {!   !}

unite-divide : ∀ {F} (fx : A × ⟦ Δ F ⟧₂ ⊥ A ⊎ ⟦ F ⟧₁ ⊥) → divide {F = F} (unite {F = F} fx) ≡ fx
unite-divide {F = Const A} (inj₂ x) = refl
unite-divide {F = Id} (inj₁ x) = refl
unite-divide {F = F +̂ G} (inj₁ x) = {!   !}
unite-divide {F = F +̂ G} (inj₂ y) = {!   !}
unite-divide {F = F ×̂ G} (inj₁ x) = {!   !}
unite-divide {F = F ×̂ G} (inj₂ y) = {!   !}
