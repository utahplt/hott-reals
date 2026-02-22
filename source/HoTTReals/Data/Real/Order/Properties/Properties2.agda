module HoTTReals.Data.Real.Order.Properties.Properties2 where

import Cubical.Data.Bool as Bool
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic hiding (⊥; ¬_)
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary

open BinaryRelation

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Algebra.Negation
open import HoTTReals.Data.Real.Order.Addition.Addition1
open import HoTTReals.Data.Real.Order.Addition.Addition2
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Data.Real.Order.Distance

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

-- Gilbert Lemma 4.13: Cauchy reals are bounded by rationals
∣∣<rational :
  (x : ℝ) → ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ x ∣ < rational q))
∣∣<rational x = ∃-rec isPropPropTrunc χ ω
  where
  φ : 0 < 1
  φ = rationalStrictMonotone {q = 0} {r = 1} ℚ.0<1

  ψ : ∣ x ∣ < ∣ x ∣ + 1
  ψ = subst (λ y → y < ∣ x ∣ + 1)
            (+-unitʳ ∣ x ∣)
            (addLeftStrictMonotone {x = 0} {y = 1} {a = ∣ x ∣} φ)

  ω : ∃ ℚ.ℚ (λ q → (∣ x ∣ < rational q) × (rational q < ∣ x ∣ + 1))
  ω = <-archimedian ∣ x ∣ (∣ x ∣ + 1) ψ

  χ : (q : ℚ.ℚ) →
      (∣ x ∣ < rational q) × (rational q < ∣ x ∣ + 1) →
      ∃ ℚ.ℚ (λ r → (0 ℚ.< r) × (∣ x ∣ < rational r))
  χ q (π , _) = ∣ q , (ρ' , π) ∣₁
    where
    ρ : 0 < rational q
    ρ = ≤→<→< {x = 0} {y = ∣ x ∣} {z = rational q} (0≤magnitude x) π

    ρ' : 0 ℚ.< q
    ρ' = rationalStrictReflective {q = 0} {r = q} ρ

∣∣≤rational :
  (x : ℝ) → ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ x ∣ ≤ rational q))
∣∣≤rational x = PropositionalTruncation.map φ (∣∣<rational x)
  where
  φ : Σ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ x ∣ < rational q)) →
      Σ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ x ∣ ≤ rational q))
  φ (ε , (ψ , ω)) = ε , (ψ , (<→≤ {x = ∣ x ∣} {y = rational ε} ω))

approximateBelowCauchy :
  (x : ℝ) → CauchyApproximation (λ ε φ → x - rational ε)
approximateBelowCauchy x ε δ φ ψ = {!!}

≤→¬< : {x y : ℝ} → x ≤ y → ¬ y < x
≤→¬< {x} {y} φ ψ = <-irreflexive x ω 
  where
  ω : x < x
  ω = ≤→<→< {x} {y} {x} φ ψ

-- ¬<→≤ : {x y : ℝ} → ¬ x < y → y ≤ x
-- ¬<→≤ {x} {y} = {!!}

-- ≤↔¬< : (x y : ℝ) → (x ≤ y) ↔ (¬ y < x)
-- ≤↔¬< x y = ≤→¬< {x} {y} , ¬<→≤ {y} {x}
