module HoTTReals.Data.Real.Order.Addition.Addition1 where

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

open import HoTTReals.Data.Real.Algebra.Negation
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Order.Base

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

min+maxLipschitz₁ : (y : ℝ) → Lipschitzℝ (λ x → min x y + max x y) 2 ℚ.0<2
min+maxLipschitz₁ y =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    (minLipschitz₁ y) (maxLipschitz₁ y) +lipschitz₁ +lipschitz₂

min+maxLipschitz₂ : (x : ℝ) → Lipschitzℝ (λ y → min x y + max x y) 2 ℚ.0<2
min+maxLipschitz₂ x =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    (minLipschitz₂ x) (maxLipschitz₂ x) +lipschitz₁ +lipschitz₂

min+maxContinuous₁ : (y : ℝ) → Continuous (λ x → min x y + max x y)
min+maxContinuous₁ y =
  lipschitz→continuous
    (λ x → min x y + max x y)
    2 ℚ.0<2
    (min+maxLipschitz₁ y)

min+maxContinuous₂ : (x : ℝ) → Continuous (λ y → min x y + max x y)
min+maxContinuous₂ x =
  lipschitz→continuous
    (λ y → min x y + max x y)
    2 ℚ.0<2
    (min+maxLipschitz₂ x)

min+max≡+ : (x y : ℝ) → min x y + max x y ≡ x + y
min+max≡+ =
  continuousExtensionLaw₂
    (λ x y → min x y + max x y)
    _+_
    (λ q r → ℚ.min q r ℚ.+ ℚ.max q r)
    ℚ._+_
    φ ψ ω
    χ π ρ σ
  where
  φ : (q r : ℚ.ℚ) →
      min (rational q) (rational r) + max (rational q) (rational r) ≡
      rational (ℚ.min q r ℚ.+ ℚ.max q r)
  φ q r =
    min (rational q) (rational r) + max (rational q) (rational r)
      ≡⟨ cong (flip _+_ (max (rational q) (rational r)))
              (liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ q r) ⟩
    rational (ℚ.min q r) + max (rational q) (rational r)
      ≡⟨ cong (_+_ (rational (ℚ.min q r)))
                   (liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ q r) ⟩
    rational (ℚ.min q r) + rational (ℚ.max q r)
      ≡⟨ liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂
                                    (ℚ.min q r) (ℚ.max q r) ⟩
    rational (ℚ.min q r ℚ.+ ℚ.max q r) ∎

  ψ : (q r : ℚ.ℚ) → rational q + rational r ≡ rational (q ℚ.+ r)
  ψ = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

  ω : (q r : ℚ.ℚ) → ℚ.min q r ℚ.+ ℚ.max q r ≡ q ℚ.+ r
  ω = ℚ.min+max≡+

  χ : (u : ℝ) → Continuous $ (λ y → min u y + max u y)
  χ = min+maxContinuous₂

  π : (v : ℝ) → Continuous $ flip (λ x y → min x y + max x y) v
  π = min+maxContinuous₁

  ρ : (u : ℝ) → Continuous $ _+_ u
  ρ = +continuous₂

  σ : (v : ℝ) → Continuous $ flip _+_ v
  σ = +continuous₁

max≡→min≡ : {x y : ℝ} → max x y ≡ y → min x y ≡ x
max≡→min≡ {x} {y} φ = ψ
  where
  φ' : min x y + y ≡ x + y
  φ' = cong (_+_ $ min x y) (sym φ) ∙ min+max≡+ x y

  ψ : min x y ≡ x
  ψ = GroupTheory.·CancelR ℝGroup y φ'

min≡→max≡ : {x y : ℝ} → min x y ≡ x → max x y ≡ y
min≡→max≡ {x} {y} φ = ψ
  where
  φ' : x + max x y ≡ x + y
  φ' = cong (flip _+_ $ max x y) (sym φ) ∙ min+max≡+ x y

  ψ : max x y ≡ y
  ψ = GroupTheory.·CancelL ℝGroup x φ'

maxNegateNegateLipschitz₁ :
  (y : ℝ) → Lipschitzℝ (λ x → max (- x) (- y)) 2 ℚ.0<2
maxNegateNegateLipschitz₁ y =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    -lipschitzℝ (constantLipschitzℝ (- y)) maxLipschitz₁ maxLipschitz₂

maxNegateNegateLipschitz₂ :
  (x : ℝ) → Lipschitzℝ (λ y → max (- x) (- y)) 2 ℚ.0<2
maxNegateNegateLipschitz₂ x =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    (constantLipschitzℝ (- x)) -lipschitzℝ maxLipschitz₁ maxLipschitz₂

maxNegateNegateContinuous₁ : (y : ℝ) → Continuous (λ x → max (- x) (- y))
maxNegateNegateContinuous₁ y =
  lipschitz→continuous
    (λ x → max (- x) (- y))
    2 ℚ.0<2
    (maxNegateNegateLipschitz₁ y)

maxNegateNegateContinuous₂ : (x : ℝ) → Continuous (λ y → max (- x) (- y))
maxNegateNegateContinuous₂ x =
  lipschitz→continuous
    (λ y → max (- x) (- y))
    2 ℚ.0<2
    (maxNegateNegateLipschitz₂ x)

negateMaxNegateNegate≡min : (x y : ℝ) → - max (- x) (- y) ≡ min x y
negateMaxNegateNegate≡min =
  continuousExtensionLaw₂
    (λ x y → - max (- x) (- y)) min
    (λ q r → ℚ.- ℚ.max (ℚ.- q) (ℚ.- r)) ℚ.min
    φ ψ ω χ π ρ σ
  where
  φ : (q r : ℚ.ℚ) →
      - max (- rational q) (- rational r) ≡
      rational (ℚ.- ℚ.max (ℚ.- q) (ℚ.- r))
  φ q r = - max (- rational q) (- rational r)
            ≡⟨ cong (λ ?x → - max ?x (- rational r))
                    (liftLipschitz≡rational
                      (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ q) ⟩
          - max (rational (ℚ.- q)) (- rational r)
            ≡⟨ cong (λ ?x → - max (rational (ℚ.- q)) ?x)
                    (liftLipschitz≡rational
                      (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ r) ⟩
          - max (rational (ℚ.- q)) (rational (ℚ.- r))
            ≡⟨ cong -_ (liftNonexpanding₂≡rational
                         ℚ.max maxNonexpandingℚ₂ (ℚ.- q) (ℚ.- r)) ⟩
          - rational (ℚ.max (ℚ.- q) (ℚ.- r))
            ≡⟨ liftLipschitz≡rational
                 (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ (ℚ.max (ℚ.- q) (ℚ.- r)) ⟩
          rational (ℚ.- (ℚ.max (ℚ.- q) (ℚ.- r))) ∎

  ψ : (q r : ℚ.ℚ) → min (rational q) (rational r) ≡ rational (ℚ.min q r)
  ψ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂

  ω : (q r : ℚ.ℚ) → (ℚ.- ℚ.max (ℚ.- q) (ℚ.- r)) ≡ ℚ.min q r
  ω = ℚ.negateMaxNegateNegate≡min

  χ : (u : ℝ) → Continuous $ (λ y → - max (- u) (- y))
  χ u = continuousCompose
          (λ y → max (- u) (- y)) -_
          (maxNegateNegateContinuous₂ u) -continuous

  π : (v : ℝ) → Continuous $ flip (λ x y → - max (- x) (- y)) v
  π v = continuousCompose
          (λ x → max (- x) (- v)) -_
          (maxNegateNegateContinuous₁ v) -continuous

  ρ : (u : ℝ) → Continuous $ min u
  ρ = minContinuous₂

  σ : (v : ℝ) → Continuous $ flip min v
  σ = minContinuous₁

negateMinNegateNegate≡max : (x y : ℝ) → - min (- x) (- y) ≡ max x y
negateMinNegateNegate≡max x y = ψ
  where
  φ : - max (- - x) (- - y) ≡ min (- x) (- y)
  φ = negateMaxNegateNegate≡min (- x) (- y)

  φ' : max (- - x) (- - y) ≡ - min (- x) (- y)
  φ' = sym (-involutive _) ∙ cong -_ φ

  ψ : - min (- x) (- y) ≡ max x y
  ψ = sym φ' ∙ cong₂ max (-involutive x) (-involutive y)

-antitone≤ : {x y : ℝ} → x ≤ y → - y ≤ - x
-antitone≤ {x} {y} φ = π
  where
  ψ : min x y ≡ x
  ψ = max≡→min≡ φ

  ω : - max (- x) (- y) ≡ x
  ω = negateMaxNegateNegate≡min x y ∙ ψ

  χ : max (- x) (- y) ≡ - x
  χ = sym (-involutive _) ∙ cong -_ ω

  π : max (- y) (- x) ≡ - x
  π = maxCommutative (- y) (- x) ∙ χ

-antitone< : {x y : ℝ} → x < y → - y < - x
-antitone< {x} {y} = ∃-rec (<-isProp (- y) (- x)) φ
  where
  φ : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) × ((fst u) ℚ.< (snd u)) × (rational (snd u) ≤ y) →
      - y < - x
  φ (q , r) (ψ , ω , χ) = ∣ (ℚ.- r , ℚ.- q) , (χ' , ω' , ψ') ∣₁
    where
    χ' : - y ≤ rational (ℚ.- r)
    χ' = -antitone≤ {x = rational r} {y = y} χ

    ω' : ℚ.- r ℚ.< ℚ.- q
    ω' = ℚ.<antitone- {x = q} {y = r} ω

    ψ' : rational (ℚ.- q) ≤ - x
    ψ' = -antitone≤ {x = x} {y = rational q} ψ

maxAddLeft : (a x y : ℝ) →
  max (a + x) (a + y) ≡ a + max x y
maxAddLeft =
  continuousExtensionLaw₃ f g f' g' φ ψ ω χ π ρ σ τ υ
  where
  f : ℝ → ℝ → ℝ → ℝ
  f a x y = max (a + x) (a + y)

  g : ℝ → ℝ → ℝ → ℝ
  g a x y = a + max x y

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' a x y = ℚ.max (a ℚ.+ x) (a ℚ.+ y)

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' a x y = a ℚ.+ ℚ.max x y

  α : (q r : ℚ.ℚ) → rational q + rational r ≡ rational (q ℚ.+ r)
  α = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

  β : (q r : ℚ.ℚ) → max (rational q) (rational r) ≡ rational (ℚ.max q r)
  β = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂

  φ : (a x y : ℚ.ℚ) →
      f (rational a) (rational x) (rational y) ≡ rational (f' a x y)
  φ a x y =
    max (rational a + rational x) (rational a + rational y)
      ≡⟨ cong₂ max (α a x) (α a y) ⟩
    max (rational (a ℚ.+ x)) (rational (a ℚ.+ y))
      ≡⟨ β (a ℚ.+ x) (a ℚ.+ y) ⟩
    rational (ℚ.max (a ℚ.+ x) (a ℚ.+ y)) ∎

  ψ : (a x y : ℚ.ℚ) →
      g (rational a) (rational x) (rational y) ≡ rational (g' a x y)
  ψ a x y =
    rational a + max (rational x) (rational y)
      ≡⟨ cong (rational a +_) (β x y) ⟩
    rational a + rational (ℚ.max x y)
      ≡⟨ α a (ℚ.max x y) ⟩
    rational (a ℚ.+ ℚ.max x y) ∎

  ω : (a x y : ℚ.ℚ) → f' a x y ≡ g' a x y
  ω a x y = ℚ.maxAddLeft a x y

  χ : (a x : ℝ) → Continuous (f a x)
  χ a x = continuousCompose
            (a +_) (max (a + x))
            (+continuous₂ a) (maxContinuous₂ (a + x))

  π : (a y : ℝ) → Continuous (λ x → f a x y)
  π a y = continuousCompose
            (a +_) (flip max (a + y))
            (+continuous₂ a) (maxContinuous₁ (a + y))

  ρ : (x y : ℝ) → Continuous (λ a → f a x y)
  ρ x y = lipschitz→continuous (λ a → f a x y) 2 ℚ.0<2
            (lipschitz₂-composeLipschitz₁-lipschitz
              1 1 1 1 ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
              (+lipschitz₁ x) (+lipschitz₁ y) maxLipschitz₁ maxLipschitz₂)

  σ : (a x : ℝ) → Continuous (g a x)
  σ a x = continuousCompose
            (max x) (a +_)
            (maxContinuous₂ x) (+continuous₂ a)

  τ : (a y : ℝ) → Continuous (λ x → g a x y)
  τ a y = continuousCompose
            (flip max y) (a +_)
            (maxContinuous₁ y) (+continuous₂ a)

  υ : (x y : ℝ) → Continuous (λ a → g a x y)
  υ x y = +continuous₁ (max x y)

maxAddRight :
  (a x y : ℝ) → max (x + a) (y + a) ≡ max x y + a
maxAddRight a x y =
  max (x + a) (y + a)
    ≡⟨ cong₂ max (+-commutative x a) (+-commutative y a) ⟩
  max (a + x) (a + y)
    ≡⟨ maxAddLeft a x y ⟩
  a + max x y
    ≡⟨ +-commutative a (max x y) ⟩
  max x y + a ∎

addLeftMonotone : {x y a : ℝ} → x ≤ y → a + x ≤ a + y
addLeftMonotone {x} {y} {a} φ =
  max (a + x) (a + y)
    ≡⟨ maxAddLeft a x y ⟩
  a + max x y
    ≡⟨ cong (_+_ a) φ ⟩
  a + y ∎

addRightMonotone : {x y a : ℝ} → x ≤ y → x + a ≤ y + a
addRightMonotone {x} {y} {a} φ =
  max (x + a) (y + a)
    ≡⟨ cong₂ max (+-commutative x a) (+-commutative y a) ⟩
  max (a + x) (a + y)
    ≡⟨ addLeftMonotone {x = x} {y = y} {a = a} φ ⟩
  a + y
    ≡⟨ +-commutative a y ⟩
  y + a ∎

addLeftReflective : {x y a : ℝ} → a + x ≤ a + y → x ≤ y
addLeftReflective {x} {y} {a} φ = ψ'
  where
  ψ : (- a) + (a + x) ≤ (- a) + (a + y)
  ψ = addLeftMonotone {a + x} {a + y} { - a } φ

  ψ' : x ≤ y
  ψ' = subst2 _≤_ (negateAddCancelLeft a x) (negateAddCancelLeft a y) ψ

addRightReflective : {x y a : ℝ} → x + a ≤ y + a → x ≤ y
addRightReflective {x} {y} {a} φ = ψ'
  where
  φ' : a + x ≤ a + y
  φ' = subst2 _≤_ (+-commutative x a) (+-commutative y a) φ

  ψ' : x ≤ y
  ψ' = addLeftReflective {x} {y} {a} φ'
