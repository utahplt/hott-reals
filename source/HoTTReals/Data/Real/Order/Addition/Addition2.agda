module HoTTReals.Data.Real.Order.Addition.Addition2 where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order

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
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Properties.Properties1

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

addLeftStrictMonotone : {x y a : ℝ} → x < y → a + x < a + y
addLeftStrictMonotone {x} {y} {a} φ = χ
  where
  ψ = <→∃+ε≤ {x = x} {y = y} φ

  ω : (ε : ℚ.ℚ) →
      (0 ℚ.< ε) × (x + rational ε ≤ y) →
      a + x < a + y
  ω ε (χ , π) = τ
    where
    ρ : a + (x + rational ε) ≤ a + y
    ρ = addLeftMonotone {x = x + rational ε} {y = y} {a = a} π

    ρ' : (a + x) + rational ε ≤ a + y
    ρ' = subst (flip _≤_ $ a + y) (sym $ +-associative a x (rational ε)) ρ

    σ : ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × ((a + x) + rational ε ≤ a + y))
    σ = ∣ ε , (χ , ρ') ∣₁

    τ : a + x < a + y
    τ = ∃+ε≤→< {x = a + x} {y = a + y} σ

  χ : a + x < a + y
  χ = ∃-rec (<-isProp (a + x) (a + y)) ω ψ

addRightStrictMonotone : {x y a : ℝ} → x < y → x + a < y + a
addRightStrictMonotone {x} {y} {a} φ = ψ'
  where
  ψ : a + x < a + y
  ψ = addLeftStrictMonotone {x} {y} {a} φ

  ψ' : x + a < y + a
  ψ' = subst2 _<_ (+-commutative a x) (+-commutative a y) ψ
