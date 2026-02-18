module HoTTReals.Data.Real.Order.Magnitude where

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
open import HoTTReals.Data.Real.Order.Addition.Addition1

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

∣_∣' : ℝ → ℝ
∣_∣' = liftLipschitz
         (rational ∘ ℚ.∣_∣)
         1 ℚ.0<1
         (nonexpandingℚ→lipschitzℚ ℚ.∣_∣ ℚ.magnitudeNonexpanding)

magnitude'Lipschitzℝ : Lipschitzℝ ∣_∣' 1 ℚ.0<1
magnitude'Lipschitzℝ =
  let φ = liftLipschitzLipschitz
            (rational ∘ ℚ.∣_∣) 1 ℚ.0<1
            (nonexpandingℚ→lipschitzℚ ℚ.∣_∣ ℚ.magnitudeNonexpanding)
  in φ

magnitude'Nonexpandingℝ : Nonexpandingℝ ∣_∣'
magnitude'Nonexpandingℝ = lipschitzℝ→nonexpandingℝ ∣_∣' magnitude'Lipschitzℝ

magnitude'Continuous : Continuous ∣_∣'
magnitude'Continuous = lipschitz→continuous ∣_∣' 1 ℚ.0<1 magnitude'Lipschitzℝ

∣_∣ : ℝ → ℝ
∣ x ∣ = max x (- x)

magnitudeExtendsRationalMagnitude : 
  (∣_∣ ∘ rational) ∼ (rational ∘ ℚ.∣_∣)
magnitudeExtendsRationalMagnitude q =
  max (rational q) (- rational q)
    ≡⟨ cong (max (rational q))
            (liftLipschitz≡rational (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ q) ⟩
  max (rational q) (rational $ ℚ.- q)
    ≡⟨ liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ q (ℚ.- q) ⟩
  rational (ℚ.max q (ℚ.- q)) ∎

magnitudeLipschitzℝ : Lipschitzℝ ∣_∣ 2 ℚ.0<2
magnitudeLipschitzℝ u v ε φ ψ = σ'
  where
  ω : Close ε φ (- u) (- v)
  ω = -nonexpandingℝ u v ε φ ψ

  χ : Close ε φ (max u (- u)) (max u (- v))
  χ = snd maxNonexpandingℝ₂ u (- u) (- v) ε φ ω

  π : Close ε φ (max u (- v)) (max v (- v))
  π = fst maxNonexpandingℝ₂ (- v) u v ε φ ψ

  ρ : Close (ε ℚ.+ ε) (ℚ.0<+' {x = ε} {y = ε} φ φ) (max u (- u)) (max v (- v))
  ρ = closeTriangleInequality
        (max u (- u)) (max u (- v)) (max v (- v))
        ε ε φ φ
        χ π

  σ : Σ (0 ℚ.< 2 ℚ.· ε)
        (λ ξ → Close (2 ℚ.· ε) ξ (max u (- u)) (max v (- v)))
  σ = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ _ _))
            (ℚ.self+≡2· ε)
            ((ℚ.0<+' {x = ε} {y = ε} φ φ) , ρ)

  σ' : Close (2 ℚ.· ε) (ℚ.0<· {x = 2} {y = ε} ℚ.0<2 φ) (max u (- u)) (max v (- v))
  σ' = subst (λ ?ξ → Close (2 ℚ.· ε) ?ξ (max u (- u)) (max v (- v)))
             (ℚ.isProp< 0 (2 ℚ.· ε) (fst σ) (ℚ.0<· {x = 2} {y = ε} ℚ.0<2 φ))
             (snd σ)

magnitudeContinuous : Continuous ∣_∣
magnitudeContinuous = lipschitz→continuous ∣_∣ 2 ℚ.0<2 magnitudeLipschitzℝ

magnitude∼magnitude' : ∣_∣ ∼ ∣_∣'
magnitude∼magnitude' =
  continuousExtensionLaw₁ ∣_∣ ∣_∣' ℚ.∣_∣ ℚ.∣_∣
  φ ψ ω
  χ π
  where
  φ : (∣_∣ ∘ rational) ∼ (rational ∘ ℚ.∣_∣)
  φ = magnitudeExtendsRationalMagnitude

  ψ : (∣_∣' ∘ rational) ∼ (rational ∘ ℚ.∣_∣)
  ψ = liftLipschitz≡rational
        (rational ∘ ℚ.∣_∣)
        1 ℚ.0<1
        (nonexpandingℚ→lipschitzℚ ℚ.∣_∣ ℚ.magnitudeNonexpanding)

  ω : ℚ.∣_∣ ∼ ℚ.∣_∣
  ω q = refl

  χ : Continuous ∣_∣
  χ = magnitudeContinuous

  π : Continuous ∣_∣'
  π = magnitude'Continuous

magnitude≡magnitude' : ∣_∣ ≡ ∣_∣'
magnitude≡magnitude' = funExt magnitude∼magnitude'

magnitudeNonexpandingℝ : Nonexpandingℝ ∣_∣
magnitudeNonexpandingℝ =
  subst Nonexpandingℝ (sym magnitude≡magnitude') magnitude'Nonexpandingℝ

magnitudeNegate≡magnitude : (x : ℝ) → ∣ - x ∣ ≡ ∣ x ∣
magnitudeNegate≡magnitude x =
  max (- x) (- - x)
    ≡⟨ cong (max (- x)) (-involutive x) ⟩
  max (- x) x
    ≡⟨ maxCommutative (- x) x ⟩
  max x (- x) ∎

self≤∣∣ : (x : ℝ) → x ≤ ∣ x ∣
self≤∣∣ x = ≤-max₁ x (- x)

-∣∣≤self : (x : ℝ) → - ∣ x ∣ ≤ x
-∣∣≤self x = ω
  where
  φ : - x ≤ ∣ - x ∣
  φ = self≤∣∣ (- x)

  ψ : - ∣ - x ∣ ≤ - - x
  ψ = -antitone≤ {x = - x} {y = ∣ - x ∣} φ 

  ω : - ∣ x ∣ ≤ x
  ω = subst2 _≤_ (cong -_ (magnitudeNegate≡magnitude x)) (-involutive x) ψ

≡0→magnitude≡0 : {x : ℝ} → x ≡ 0 → ∣ x ∣ ≡ 0
≡0→magnitude≡0 {x} φ = ω
  where
  ψ : ∣ 0 ∣ ≡ 0
  ψ = refl

  ω : ∣ x ∣ ≡ 0
  ω = cong ∣_∣ φ ∙ ψ

magnitudeMagnitude≡magnitude : (x : ℝ) → ∣ ∣ x ∣ ∣ ≡ ∣ x ∣
magnitudeMagnitude≡magnitude x = χ
  where
  φ : - ∣ x ∣ ≤ x
  φ = -∣∣≤self x

  ψ : x ≤ ∣ x ∣
  ψ = self≤∣∣ x

  ω : - ∣ x ∣ ≤ ∣ x ∣
  ω = ≤-transitive (- ∣ x ∣) x ∣ x ∣ φ ψ

  χ : max ∣ x ∣ (- ∣ x ∣) ≡ ∣ x ∣
  χ = maxCommutative ∣ x ∣ (- ∣ x ∣) ∙ ω

-- TODO:
-- magnitude≡0→≡0 : {x : ℝ} → ∣ x ∣ ≡ 0 → x ≡ 0
-- magnitude≡0→≡0 {x} φ = {!!}

0≤magnitude : (x : ℝ) → 0 ≤ ∣ x ∣
0≤magnitude =
  continuousExtensionLaw₁
    f g f' g'
    H K L φ ψ
  where
  f : ℝ → ℝ
  f x = max 0 (max x (- x))

  g : ℝ → ℝ
  g = ∣_∣

  f' : ℚ.ℚ → ℚ.ℚ
  f' q = ℚ.max 0 (ℚ.∣ q ∣)

  g' : ℚ.ℚ → ℚ.ℚ
  g' = ℚ.∣_∣

  H : (f ∘ rational) ∼ (rational ∘ f')
  H q = max 0 ∣ rational q ∣
          ≡⟨ cong (max 0) (magnitudeExtendsRationalMagnitude q) ⟩
        max 0 (rational (ℚ.∣ q ∣))
          ≡⟨ liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 0 (ℚ.∣ q ∣) ⟩
        rational (ℚ.max 0 (ℚ.∣ q ∣)) ∎

  K : (g ∘ rational) ∼ (rational ∘ g')
  K = magnitudeExtendsRationalMagnitude

  L : f' ∼ g'
  L q = ℚ.≤→max 0 ℚ.∣ q ∣ (ℚ.0≤∣∣ q)

  φ : Continuous f
  φ = continuousCompose ∣_∣ (max 0) magnitudeContinuous (maxContinuous₂ 0)

  ψ : Continuous g
  ψ = magnitudeContinuous
