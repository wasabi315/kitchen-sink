# iso

Normalisation of dependent types up to isomorphism. Curries functions that take pairs and right-nests sigma types, computing a witness isomorphism and a conversion function (transport along the isomorphism) via NbE.

```text
(F : (U × U → U) → U) (G : U × U → U) → F G

  ↓ ΠL (ΠL Curry) · ΠR (ΠL Curry)

(F : (U → U → U) → U) (G : U → U → U) → F (λ x y. G x y)

conversion function:
  λ x x₀ x₁. x (λ x₂. x₀ (λ x₃ y. x₂ (x₃ , y))) (λ p. x₁ p.1 p.2)


(F : U × U → U) (A : U) (B : U) → F (A , B)

  ↓ ΠL Curry

(F : U → U → U) (A : U) (B : U) → F A B

conversion function:
  λ x x₀. x (λ p. x₀ p.1 p.2)


(A : U) (B : A → U) (P : (x : A) × B x → U) (p : (x : A) × B x) (q : (y : A) × B y) → P p × P q

  ↓ ΠR (ΠR (ΠL Curry · ΠR (Curry · ΠR (ΠR Curry))))

(A : U) (B : A → U) (P : (x : A) → B x → U) (x : A) (p : B x) (y : A) (q : B y) → P x p × P y q

conversion function:
  λ x x₀ x₁ x₂ x₃ x₄ x₅ y. x x₀ x₁ (λ p. x₂ p.1 p.2) (x₃ , x₄) (x₅ , y)
```
