module HoTTReals.Data.Real.Definitions where

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import HoTTReals.Data.Real.Base

open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

-- HoTT 385, dependent Cauchy approximation
CauchyApproximation' :
  {i j : Level}
  (A : ℝ → Type i)
  (B : {x y : ℝ} → A x → A y → {ε : ℚ} {p : 0 < ε} → x ∼[ ε , p ] y → Type j)
  (x : (ε : ℚ) → 0 < ε → ℝ) →
  CauchyApproximation x →
  ((ε : ℚ) (p : 0 < ε) → A $ x ε p) →
  Type j
CauchyApproximation' A B x p a =
  (δ ε : ℚ) (q : 0 < δ) (r : 0 < ε) →
  B (a δ q) (a ε r) (p δ ε q r)

CauchyApproximation'' : 
  {i j : Level}
  (A : Type i)
  (B : (a b : A) → (ε : ℚ) → 0 < ε → Type j) →
  (f : (ε : ℚ) → 0 < ε → A) →
  Type j
CauchyApproximation'' A B f =
  (ε δ : ℚ) (ψ : 0 < ε) (θ : 0 < δ) →
  B (f ε ψ) (f δ θ) (ε + δ) (0<+' {x = ε} {y = δ} ψ θ)

-- HoTT Definition 11.3.14
Lipschitzℚ : (f : ℚ → ℝ) (L : ℚ) → 0 < L → Type ℓ-zero
Lipschitzℚ f L φ =
  (q r ε : ℚ) (ψ : 0 < ε) →
  ∣ q - r ∣ < ε →
  f q ∼[ L · ε , 0<· {x = L} {y = ε} φ ψ ] f r

Lipschitzℝ : (f : ℝ → ℝ) (L : ℚ) → 0 < L → Type ℓ-zero
Lipschitzℝ f L φ =
  (u v : ℝ)
  (ε : ℚ) (ψ : 0 < ε) →
  u ∼[ ε , ψ ] v →
  f u ∼[ L · ε , 0<· {x = L} {y = ε} φ ψ ] f v

Nonexpandingℚ₂ : (ℚ → ℚ → ℚ) → Type ℓ-zero
Nonexpandingℚ₂ f =
  ((q r s : ℚ) → distance (f q s) (f r s) ≤ distance q r) ×
  ((q r s : ℚ) → distance (f q r) (f q s) ≤ distance r s)

Nonexpandingℝ₂ : (ℝ → ℝ → ℝ) → Type ℓ-zero
Nonexpandingℝ₂ f =
  ((u v w : ℝ)
   (ε : ℚ) (φ : 0 < ε) →
   u ∼[ ε , φ ] v → f u w ∼[ ε , φ ] f v w) ×
  ((u v w : ℝ)
   (ε : ℚ) (φ : 0 < ε) →
   v ∼[ ε , φ ] w → f u v ∼[ ε , φ ] f u w)

Open : {i : Level}
       (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i) →
       ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
       Type i
Open B _ =
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) →
  B ε φ u v →
  ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ ψ → B (ε - θ) ψ u v))

Monotone : {i : Level}
           (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i) →
           ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
           Type i
Monotone B _ =
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) →
  ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ ψ → B (ε - θ) ψ u v)) →
  B ε φ u v

-- HoTT 11.3.21
Rounded : {i : Level}
          (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i) →
          ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
          Type i
Rounded B φ =
  (u v : ℝ) (ε : ℚ) (ψ : 0 < ε) →
  B ε ψ u v ↔ ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ ψ → B (ε - θ) ψ u v))

-- HoTT 11.3.22
TriangleInequality₁ :
  {i j : Level}
  (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i)
  (C : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type j) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (C ε φ u v)) →
  Type (ℓ-max i j)
TriangleInequality₁ B C _ _ =
  (u v w : ℝ)
  (ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) →
  C ε φ u v → B δ ψ v w → C (ε + δ) (0<+' {x = ε} {y = δ} φ ψ) u w

-- HoTT 11.3.23
TriangleInequality₂ :
  {i j : Level}
  (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i)
  (C : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type j) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (C ε φ u v)) →
  Type (ℓ-max i j)
TriangleInequality₂ B C _ _ =
  (u v w : ℝ)
  (ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) →
  B ε φ u v → C δ ψ v w → C (ε + δ) (0<+' {x = ε} {y = δ} φ ψ) u w

TriangleInequality :
  {i : Level}
  (B : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type i) →
  ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (B ε φ u v)) →
  Type i
TriangleInequality B _ =
  (u v w : ℝ)
  (ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) →
  B ε φ u v → B δ ψ v w → B (ε + δ) (0<+' {x = ε} {y = δ} φ ψ) u w

ContinuousAt : (ℝ → ℝ) → ℝ → Type
ContinuousAt f u = 
  (ε : ℚ) (φ : 0 < ε) →
  ∃ ℚ (λ δ → Σ (0 < δ) (λ ψ → (v : ℝ) → u ∼[ δ , ψ ] v → f u ∼[ ε , φ ] f v))

Continuous : (ℝ → ℝ) → Type
Continuous f = (u : ℝ) → ContinuousAt f u
