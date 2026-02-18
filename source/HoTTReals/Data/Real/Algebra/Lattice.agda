module HoTTReals.Data.Real.Algebra.Lattice where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Nat.Literals public
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Homotopy.Base

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

maxNonexpandingℚ₂ : Nonexpandingℚ₂ ℚ.max
maxNonexpandingℚ₂ = φ , ψ
  where
  φ : (s : ℚ.ℚ) → Nonexpandingℚ (flip ℚ.max s)
  φ s q r = ℚ.maxNonexpandingˡ q r s

  ψ : (q : ℚ.ℚ) → Nonexpandingℚ (ℚ.max q)
  ψ q r s = ℚ.maxNonexpandingʳ q r s

max : ℝ → ℝ → ℝ
max = liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂

maxNonexpandingℝ₂ : Nonexpandingℝ₂ max
maxNonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ.max maxNonexpandingℚ₂

maxLipschitz₁ : (v : ℝ) → Lipschitzℝ (flip max v) 1 ℚ.0<1
maxLipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ max maxNonexpandingℝ₂

maxLipschitz₂ : (u : ℝ) → Lipschitzℝ (max u) 1 ℚ.0<1
maxLipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ max maxNonexpandingℝ₂

maxContinuous₁ : (v : ℝ) → Continuous (flip max v)
maxContinuous₁ v = lipschitz→continuous (flip max v) 1 ℚ.0<1 (maxLipschitz₁ v)

maxContinuous₂ : (u : ℝ) → Continuous (max u)
maxContinuous₂ u = lipschitz→continuous (max u) 1 ℚ.0<1 (maxLipschitz₂ u)

-- Same deal as x + (- x), see comment above
maxMaxLipschitz : Lipschitzℝ (λ u → max u u) 2 ℚ.0<2
maxMaxLipschitz =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    identityLipschitzℝ identityLipschitzℝ maxLipschitz₁ maxLipschitz₂

maxAssociative : (x y z : ℝ) → max (max x y) z ≡ max x (max y z)
maxAssociative =
  continuousExtensionLaw₃
    associateℝₗ associateℝᵣ associateℚₗ associateℚᵣ
    ψ ω χ π ρ σ τ υ ξ
  where
  associateℝₗ : ℝ → ℝ → ℝ → ℝ
  associateℝₗ x y z = max (max x y) z

  associateℝᵣ : ℝ → ℝ → ℝ → ℝ
  associateℝᵣ x y z = max x (max y z)

  associateℚₗ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚₗ q r s = ℚ.max (ℚ.max q r) s

  associateℚᵣ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚᵣ q r s = ℚ.max q (ℚ.max r s)

  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.max q r)
  φ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 

  ψ : (q r s : ℚ.ℚ) →
      associateℝₗ (rational q) (rational r) (rational s) ≡
      rational (associateℚₗ q r s)
  ψ q r s =
    max (max (rational q) (rational r)) (rational s)
      ≡⟨ cong (flip max $ rational s) (φ q r) ⟩
    max (rational (ℚ.max q r)) (rational s)
      ≡⟨ φ (ℚ.max q r) s ⟩
    rational (ℚ.max (ℚ.max q r) s) ∎

  ω : (q r s : ℚ.ℚ) →
      associateℝᵣ (rational q) (rational r) (rational s) ≡
      rational (associateℚᵣ q r s)
  ω q r s =
    max (rational q) (max (rational r) (rational s))
      ≡⟨ cong (max $ rational q) (φ r s) ⟩
    max (rational q) (rational (ℚ.max r s))
      ≡⟨ φ q (ℚ.max r s) ⟩
    rational (ℚ.max q (ℚ.max r s)) ∎

  χ : (q r s : ℚ.ℚ) → associateℚₗ q r s ≡ associateℚᵣ q r s
  χ q r s = sym $ ℚ.maxAssoc q r s

  π : (x y : ℝ) → Continuous (associateℝₗ x y)
  π x y = maxContinuous₂ (max x y)

  ρ : (x z : ℝ) → Continuous (λ y → associateℝₗ x y z)
  ρ x z = continuousCompose (max x) (flip max z)
                            (maxContinuous₂ x) (maxContinuous₁ z)

  σ : (y z : ℝ) → Continuous (λ x → associateℝₗ x y z)
  σ y z = continuousCompose (flip max y) (flip max z)
                            (maxContinuous₁ y) (maxContinuous₁ z)

  τ : (x y : ℝ) → Continuous (associateℝᵣ x y)
  τ x y = continuousCompose (max y) (max x)
                            (maxContinuous₂ y) (maxContinuous₂ x)

  υ : (x z : ℝ) → Continuous (λ y → associateℝᵣ x y z)
  υ x z = continuousCompose (flip max z) (max x)
                            (maxContinuous₁ z) (maxContinuous₂ x)

  ξ : (y z : ℝ) → Continuous (λ x → associateℝᵣ x y z)
  ξ y z = maxContinuous₁ (max y z)

maxCommutative : (x y : ℝ) → max x y ≡ max y x
maxCommutative =
  continuousExtensionLaw₂
    max
    (flip max)
    ℚ.max
    (flip ℚ.max)
    φ (flip φ) ψ ω χ χ ω
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.max q r)
  φ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 

  ψ : (x y : ℚ.ℚ) → ℚ.max x y ≡ ℚ.max y x
  ψ = ℚ.maxComm

  ω : (u : ℝ) → Continuous (max u)
  ω = maxContinuous₂

  χ : (v : ℝ) → Continuous $ flip max v
  χ = maxContinuous₁

maxIdempotent : (x : ℝ) → max x x ≡ x
maxIdempotent =
  continuousExtensionLaw₁
    (λ x → max x x) (idfun ℝ)
    (λ q → ℚ.max q q) (idfun ℚ.ℚ)
    ψ ω χ π ρ
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.max q r)
  φ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 

  ψ : ((λ x → max x x) ∘ rational) ∼ (rational ∘ (λ q → ℚ.max q q))
  ψ q = φ q q

  ω : (idfun ℝ ∘ rational) ∼ (rational ∘ idfun ℚ.ℚ)
  ω q = refl

  χ : (λ q → ℚ.max q q) ∼ idfun ℚ.ℚ
  χ = ℚ.maxIdem

  π : Continuous (λ x → max x x)
  π = lipschitz→continuous (λ x → max x x) 2 ℚ.0<2 maxMaxLipschitz
  
  ρ : Continuous (idfun ℝ)
  ρ = identityContinuous

minNonexpandingℚ₂ : Nonexpandingℚ₂ ℚ.min
minNonexpandingℚ₂ = φ , ψ
  where
  φ : (s : ℚ.ℚ) → Nonexpandingℚ (flip ℚ.min s)
  φ s q r = ℚ.minNonexpandingˡ q r s

  ψ : (q : ℚ.ℚ) → Nonexpandingℚ (ℚ.min q)
  ψ q r s = ℚ.minNonexpandingʳ q r s

min : ℝ → ℝ → ℝ
min = liftNonexpanding₂ ℚ.min minNonexpandingℚ₂

minNonexpandingℝ₂ : Nonexpandingℝ₂ min
minNonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ.min minNonexpandingℚ₂

minLipschitz₁ : (v : ℝ) → Lipschitzℝ (flip min v) 1 ℚ.0<1
minLipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ min minNonexpandingℝ₂

minLipschitz₂ : (u : ℝ) → Lipschitzℝ (min u) 1 ℚ.0<1
minLipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ min minNonexpandingℝ₂

minContinuous₁ : (v : ℝ) → Continuous (flip min v)
minContinuous₁ v = lipschitz→continuous (flip min v) 1 ℚ.0<1 (minLipschitz₁ v)

minContinuous₂ : (u : ℝ) → Continuous (min u)
minContinuous₂ u = lipschitz→continuous (min u) 1 ℚ.0<1 (minLipschitz₂ u)

-- Same deal as x + (- x), see comment above
minMinLipschitz : Lipschitzℝ (λ u → min u u) 2 ℚ.0<2
minMinLipschitz =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    identityLipschitzℝ identityLipschitzℝ minLipschitz₁ minLipschitz₂



minAssociative : (x y z : ℝ) → min (min x y) z ≡ min x (min y z)
minAssociative =
  continuousExtensionLaw₃
    associateℝₗ associateℝᵣ associateℚₗ associateℚᵣ
    ψ ω χ π ρ σ τ υ ξ
  where
  associateℝₗ : ℝ → ℝ → ℝ → ℝ
  associateℝₗ x y z = min (min x y) z

  associateℝᵣ : ℝ → ℝ → ℝ → ℝ
  associateℝᵣ x y z = min x (min y z)

  associateℚₗ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚₗ q r s = ℚ.min (ℚ.min q r) s

  associateℚᵣ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚᵣ q r s = ℚ.min q (ℚ.min r s)

  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.min minNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.min q r)
  φ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ 

  ψ : (q r s : ℚ.ℚ) →
      associateℝₗ (rational q) (rational r) (rational s) ≡
      rational (associateℚₗ q r s)
  ψ q r s =
    min (min (rational q) (rational r)) (rational s)
      ≡⟨ cong (flip min $ rational s) (φ q r) ⟩
    min (rational (ℚ.min q r)) (rational s)
      ≡⟨ φ (ℚ.min q r) s ⟩
    rational (ℚ.min (ℚ.min q r) s) ∎

  ω : (q r s : ℚ.ℚ) →
      associateℝᵣ (rational q) (rational r) (rational s) ≡
      rational (associateℚᵣ q r s)
  ω q r s =
    min (rational q) (min (rational r) (rational s))
      ≡⟨ cong (min $ rational q) (φ r s) ⟩
    min (rational q) (rational (ℚ.min r s))
      ≡⟨ φ q (ℚ.min r s) ⟩
    rational (ℚ.min q (ℚ.min r s)) ∎

  χ : (q r s : ℚ.ℚ) → associateℚₗ q r s ≡ associateℚᵣ q r s
  χ q r s = sym $ ℚ.minAssoc q r s

  π : (x y : ℝ) → Continuous (associateℝₗ x y)
  π x y = minContinuous₂ (min x y)

  ρ : (x z : ℝ) → Continuous (λ y → associateℝₗ x y z)
  ρ x z = continuousCompose (min x) (flip min z)
                            (minContinuous₂ x) (minContinuous₁ z)

  σ : (y z : ℝ) → Continuous (λ x → associateℝₗ x y z)
  σ y z = continuousCompose (flip min y) (flip min z)
                            (minContinuous₁ y) (minContinuous₁ z)

  τ : (x y : ℝ) → Continuous (associateℝᵣ x y)
  τ x y = continuousCompose (min y) (min x)
                            (minContinuous₂ y) (minContinuous₂ x)

  υ : (x z : ℝ) → Continuous (λ y → associateℝᵣ x y z)
  υ x z = continuousCompose (flip min z) (min x)
                            (minContinuous₁ z) (minContinuous₂ x)

  ξ : (y z : ℝ) → Continuous (λ x → associateℝᵣ x y z)
  ξ y z = minContinuous₁ (min y z)

minCommutative : (x y : ℝ) → min x y ≡ min y x
minCommutative =
  continuousExtensionLaw₂
    min
    (flip min)
    ℚ.min
    (flip ℚ.min)
    φ (flip φ) ψ ω χ χ ω
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.min minNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.min q r)
  φ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ 

  ψ : (x y : ℚ.ℚ) → ℚ.min x y ≡ ℚ.min y x
  ψ = ℚ.minComm

  ω : (u : ℝ) → Continuous (min u)
  ω = minContinuous₂

  χ : (v : ℝ) → Continuous $ flip min v
  χ = minContinuous₁
