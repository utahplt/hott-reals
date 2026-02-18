module HoTTReals.Data.Real.Lipschitz.Closed where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base

open import HoTTReals.Data.Real.Order.Base

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

-- HoTT Exercise 11.8

lipschitzClosedInterval→composeClampLipschitz :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  ((ε : ℚ.ℚ) (ω : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ ω ] f r) →
  Lipschitzℚ (f ∘ ℚ.clamp a b φ) L ψ
lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω q s ε π ρ = τ
  where
  σ : ℚ.distance (ℚ.max a (ℚ.min q b)) (ℚ.max a (ℚ.min s b)) ℚ.≤
        ℚ.distance (ℚ.min q b) (ℚ.min s b)
  σ = ℚ.maxNonexpandingʳ a (ℚ.min q b) (ℚ.min s b)

  σ' : ℚ.distance (ℚ.min q b) (ℚ.min s b) ℚ.≤ ℚ.distance q s
  σ' = ℚ.minNonexpandingˡ q s b

  σ'' : ℚ.distance (ℚ.clamp' a b φ q) (ℚ.clamp' a b φ s) ℚ.< ε
  σ'' = ℚ.isTrans≤<
          (ℚ.distance (ℚ.clamp' a b φ q) (ℚ.clamp' a b φ s))
          (ℚ.distance q s)
          ε
          (ℚ.isTrans≤
            (ℚ.distance (ℚ.clamp' a b φ q) (ℚ.clamp' a b φ s))
            (ℚ.distance (ℚ.min q b) (ℚ.min s b))
            (ℚ.distance q s)
            σ σ')
          ρ

  τ : f (ℚ.clamp a b φ q)
      ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ π ]
      f (ℚ.clamp a b φ s)
  τ = ω ε π (ℚ.clamp a b φ q) (ℚ.clamp a b φ s) σ''

liftLipschitzClosedInterval :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  ((ε : ℚ.ℚ) (ω : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ ω ] f r) →
  Σ ℝ (λ x → (rational a ≤ x) × (x ≤ rational b)) → ℝ
liftLipschitzClosedInterval a b φ f L ψ ω =
  liftLipschitz
    (f ∘ ℚ.clamp a b φ)
    L ψ
    (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω) ∘
  fst

liftLipschitzClosedIntervalLipschitz :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  (ω : (ε : ℚ.ℚ) (χ : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ χ ] f r) →
  ((ε : ℚ.ℚ) (χ : 0 ℚ.< ε)
   (x y : Σ ℝ (λ x → (rational a ≤ x) × (x ≤ rational b))) →
   fst x ∼[ ε , χ ] fst y →
   (liftLipschitzClosedInterval a b φ f L ψ ω) x
   ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ χ ]
   (liftLipschitzClosedInterval a b φ f L ψ ω) y)
liftLipschitzClosedIntervalLipschitz a b φ f L ψ ω ε χ x y π =
  liftLipschitzLipschitz
    (f ∘ ℚ.clamp a b φ)
    L ψ
    (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
    (fst x) (fst y)
    ε χ
    π

liftLipschitzClosedInterval≡rational :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  (ω : (ε : ℚ.ℚ) (χ : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ χ ] f r) →
  (q : ℚ.ℚ) (χ : a ℚ.≤ q) (π : q ℚ.≤ b) →
  (liftLipschitzClosedInterval a b φ f L ψ ω)
    (rational q , (rationalMonotone {q = a} {r = q} χ ,
                   rationalMonotone {q = q} {r = b} π)) ≡
  f (q , (χ , π))
liftLipschitzClosedInterval≡rational a b φ f L ψ ω q χ π = τ
  where
  ρ : liftLipschitz
        (λ x → f (ℚ.clamp a b φ x))
           L ψ
           (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
           (rational q) ≡
        f (ℚ.clamp a b φ q)
  ρ = liftLipschitz≡rational
        (f ∘ ℚ.clamp a b φ)
           L ψ
           (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
           q

  σ : ℚ.clamp a b φ q ≡ (q , (χ , π))
  σ = ℚ.clampFstLeftInverse a b φ (q , (χ , π))

  τ : liftLipschitz (λ x → f (ℚ.clamp a b φ x)) L ψ
       (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
       (rational q) ≡
      f (q , (χ , π))
  τ = ρ ∙ cong f σ
