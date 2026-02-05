# Iso

Type normalization via isomorphisms for dependent types.

## Overview

This implements a normalization-by-evaluation (NbE) algorithm that normalizes dependent types (Pi and Sigma types) while computing the isomorphisms witnessing the equivalence between original and normalized forms.

## Features

- **Term language**: Pi types (dependent functions), Sigma types (dependent pairs), and a universe `U`
- **Isomorphisms**: `Curry`, `Assoc`, `Comm`, and congruence rules (`Pi_cong_l`, `Pi_cong_r`, `Sigma_cong_l`, `Sigma_cong_r`)
- **Transport**: Functions that apply isomorphisms to values in both forward and backward directions

## Isomorphisms

$$
\frac{}{A \cong A} \text{Refl}
$$

$$
\frac{A \cong B}{B \cong A} \text{Sym}
$$

$$
\frac{A \cong B \quad B \cong C}{A \cong C} \text{Trans}
$$

$$
A \times B \cong B \times A \quad \text{Comm}
$$

$$
(x : (y : A) \times B[y]) \times C[x] \cong (y : A) \times (x : B[y]) \times C[(y, x)] \quad \text{Assoc}
$$

$$
(x : (y : A) \times B[y]) \to C[x] \cong (y : A) \to (x : B[y]) \to C[(y, x)] \quad \text{Curry}
$$

$$
\frac{i : A \cong A'}{(x : A) \to B[x] \cong (x : A') \to B[\text{transportInv}\ i\ x]} \Pi\text{L}
$$

$$
\frac{B[x] \cong B'[x]}{(x : A) \to B[x] \cong (x : A) \to B'[x]} \Pi\text{R}
$$

$$
\frac{i : A \cong A'}{(x : A) \times B[x] \cong (x : A') \times B[\text{transportInv}\ i\ x]} \Sigma\text{L}
$$

$$
\frac{B[x] \cong B'[x]}{(x : A) \times B[x] \cong (x : A) \times B'[x]} \Sigma\text{R}
$$

## Examples

```text
(F : (U × U → U) → U) (G : U × U → U) → F G
  ↓ ΠL (ΠL Curry) · ΠR (ΠL Curry)
(F : (U → U → U) → U) (G : U → U → U) → F (λ x x'. G x x')

(F : U × U → U) (A : U) (B : U) → F (A , B)
  ↓ ΠL Curry
(F : U → U → U) (A : U) (B : U) → F A B

(A : U) (B : A → U) (P : (x : A) × B x → U) (p : (x : A) × B x) (q : (y : A) × B y) → P p × P q
  ↓ ΠR (ΠR (ΠL Curry · ΠR (ΠR Curry · Curry)))
(A : U) (B : A → U) (P : (x : A) → B x → U) (x : A) (p : B x) (y : A) (q : B y) → P x p × P y q
```

## Reference

- [Andras Kovacs: elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
