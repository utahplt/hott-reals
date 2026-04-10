module HoTTReals.Data.Real.Order.Addition.Addition2 where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
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
  ψ : ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y))
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

addLeftStrictReflective : {x y a : ℝ} → a + x < a + y → x < y
addLeftStrictReflective {x} {y} {a} φ = ψ'
  where
  ψ : (- a) + (a + x) < (- a) + (a + y)
  ψ = addLeftStrictMonotone {a + x} {a + y} { - a } φ

  ψ' : x < y
  ψ' = subst2 _<_ (negateAddCancelLeft a x) (negateAddCancelLeft a y) ψ

addRightStrictReflective : {x y a : ℝ} → x + a < y + a → x < y
addRightStrictReflective {x} {y} {a} φ = ψ'
  where
  φ' : a + x < a + y
  φ' = subst2 _<_ (+-commutative x a) (+-commutative y a) φ

  ψ' : x < y
  ψ' = addLeftStrictReflective {x} {y} {a} φ'

+<→<- : {x y z : ℝ} → x + y < z → x < z - y
+<→<- {x} {y} {z} φ = ψ'
  where
  ψ : (x + y) - y < z - y
  ψ = addRightStrictMonotone {x = x + y} {a = - y} φ

  ψ' : x < z - y
  ψ' = subst (flip _<_ $ z - y) (addSubtractRightCancel x y) ψ

+<→<-' : {x y z : ℝ} → x + y < z → y < z - x
+<→<-' {x} {y} {z} φ =
  +<→<- {y} {x} {z} φ'
  where
  φ' : y + x < z
  φ' = subst (flip _<_ z) (+-commutative x y) φ

addPositive→leftPositive∨rightPositive :
  {x y : ℝ} →
  0 < x + y → (0 < x) ⊔′ (0 < y)
addPositive→leftPositive∨rightPositive {x} {y} φ = χ
  where
  ψ : (0 < x) ⊔′ (x < x + y)
  ψ = <-isWeaklyLinear 0 (x + y) x φ

  ω : x < x + y → 0 < y
  ω χ = π
    where
    χ' : x + 0 < x + y
    χ' = subst (flip _<_ $ x + y) (sym $ +-unitʳ x) χ

    π : 0 < y
    π = addLeftStrictReflective {0} {y} {x} χ'

  χ : (0 < x) ⊔′ (0 < y)
  χ = PropositionalTruncation.map (Sum.map (idfun _) ω) ψ
