module HoTTReals.Data.Real.Algebra.Multiplication where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.Ring.Base
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Nullary

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
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Data.Real.Order.Distance
open import HoTTReals.Data.Real.Order.Properties.Properties2

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

leftMultiplyRationalLipschitzℚ :
  (q δ : ℚ.ℚ) (φ : 0 ℚ.< δ) →
  Lipschitzℚ (rational ∘ (λ r → q ℚ.· r)) (ℚ.max ℚ.∣ q ∣ δ)
             (ℚ.isTrans<≤ 0 δ (ℚ.max ℚ.∣ q ∣ δ) φ (ℚ.≤max' ℚ.∣ q ∣ δ))
leftMultiplyRationalLipschitzℚ q δ φ r s ε ψ ω =
  rationalRational (q ℚ.· r) (q ℚ.· s) (L ℚ.· ε) (ℚ.0<· {x = L} {y = ε} σ ψ)
    (ℚ.∣∣<→<₂ {x = (q ℚ.· r) ℚ.- (q ℚ.· s)} {ε = L ℚ.· ε} τ')
    (ℚ.∣∣<→<₁ {x = (q ℚ.· r) ℚ.- (q ℚ.· s)} {ε = L ℚ.· ε} τ')
  where
  χ : (q ℚ.· r) ℚ.- (q ℚ.· s) ≡ q ℚ.· (r ℚ.- s)
  χ = (q ℚ.· r) ℚ.- (q ℚ.· s)
         ≡⟨ cong (ℚ._+_ (q ℚ.· r)) (ℚ.-·≡·- q s) ⟩
      (q ℚ.· r) ℚ.+ (q ℚ.· (ℚ.- s))
         ≡⟨ sym (ℚ.·DistL+ q r (ℚ.- s)) ⟩
      q ℚ.· (r ℚ.- s) ∎

  π : ℚ.∣ q ℚ.· (r ℚ.- s) ∣ ≡ ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣
  π = ℚ.magnitudeMultiply≡multiplyMagnitude q (r ℚ.- s)

  π' : ℚ.∣ (q ℚ.· r) ℚ.- (q ℚ.· s) ∣ ≡ ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣
  π' = ℚ.∣ (q ℚ.· r) ℚ.- (q ℚ.· s) ∣
       ≡⟨ cong ℚ.∣_∣ χ  ⟩
       ℚ.∣ q ℚ.· (r ℚ.- s) ∣
         ≡⟨ π ⟩
       ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣ ∎

  L : ℚ.ℚ
  L = ℚ.max ℚ.∣ q ∣ δ

  ρ : ℚ.∣ q ∣ ℚ.≤ L
  ρ = ℚ.≤max ℚ.∣ q ∣ δ

  ρ' : δ ℚ.≤ L
  ρ' = ℚ.≤max' ℚ.∣ q ∣ δ

  σ : 0 ℚ.< L
  σ = ℚ.isTrans<≤ 0 δ L φ ρ'

  τ : ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣ ℚ.< L ℚ.· ε
  τ = ℚ.≤→<→·<· {x = ℚ.∣ q ∣} {y = ℚ.∣ r ℚ.- s ∣} {z = L} {w = ε}
      ρ ω
        σ (ℚ.0≤∣∣ $ r ℚ.- s)

  τ' : ℚ.∣ (q ℚ.· r) ℚ.- (q ℚ.· s) ∣ ℚ.< L ℚ.· ε
  τ' = subst (ℚ._< (L ℚ.· ε)) (sym π') τ

leftMultiplyRational : 
  ℚ.ℚ → ℝ → ℝ
leftMultiplyRational q =
  liftLipschitz
    (rational ∘ λ r → q ℚ.· r)
    (ℚ.max ℚ.∣ q ∣ 1)
    (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
    (leftMultiplyRationalLipschitzℚ q 1 ℚ.0<1)

leftMultiplyRationalLipschitzℝ :
  (q : ℚ.ℚ) →
  Lipschitzℝ
    (leftMultiplyRational q)
    (ℚ.max ℚ.∣ q ∣ 1)
    (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
leftMultiplyRationalLipschitzℝ q =
  let
    -- Again, I don't know why Agda is so weird
    φ = liftLipschitzLipschitz
          (λ r → rational (q ℚ.· r))
          (ℚ.max ℚ.∣ q ∣ 1)
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
          (leftMultiplyRationalLipschitzℚ q 1 ℚ.0<1)
  in φ

leftMultiplyRationalContinuous :
  (q : ℚ.ℚ) →
  Continuous $ leftMultiplyRational q
leftMultiplyRationalContinuous q =
  lipschitz→continuous
    (leftMultiplyRational q)
    (ℚ.max ℚ.∣ q ∣ 1)
    _
    (leftMultiplyRationalLipschitzℝ q)

distanceLeftMultiplyRational≡leftMultiplyRationalDistanceₗ :
  (q r : ℚ.ℚ)
  (y : ℝ) →
  distance (leftMultiplyRational q y) (leftMultiplyRational r y) ≡
  leftMultiplyRational (ℚ.distance q r) ∣ y ∣
distanceLeftMultiplyRational≡leftMultiplyRationalDistanceₗ q r =
  continuousExtensionLaw₁ f g f' g' φ ψ ω χ π
  where
  f : ℝ → ℝ
  f y = distance (leftMultiplyRational q y) (leftMultiplyRational r y)

  g : ℝ → ℝ
  g y = leftMultiplyRational (ℚ.distance q r) ∣ y ∣

  f' : ℚ.ℚ → ℚ.ℚ
  f' s = ℚ.distance (q ℚ.· s) (r ℚ.· s)

  g' : ℚ.ℚ → ℚ.ℚ
  g' s = (ℚ.distance q r) ℚ.· ℚ.∣ s ∣

  φ : (f ∘ rational) ∼ (rational ∘ f')
  φ s = refl

  ψ : (g ∘ rational) ∼ (rational ∘ g')
  ψ s = refl

  ω : f' ∼ g'
  ω s = ℚ.·distanceᵣ s q r

  χ : Continuous f
  χ = lipschitz→continuous
           (λ x → distance (leftMultiplyRational q x)
                           (leftMultiplyRational r x))
           (1 ℚ.· (ℚ.max ℚ.∣ q ∣ 1) ℚ.+ 1 ℚ.· (ℚ.max ℚ.∣ r ∣ 1))
           _
           π
    where
    π : Lipschitzℝ
         (λ x → distance (leftMultiplyRational q x)
                         (leftMultiplyRational r x))
         (1 ℚ.· ℚ.max ℚ.∣ q ∣ 1 ℚ.+ 1 ℚ.· ℚ.max ℚ.∣ r ∣ 1)
         _
    π = lipschitz₂-composeLipschitz₁-lipschitz
          (ℚ.max ℚ.∣ q ∣ 1) (ℚ.max ℚ.∣ r ∣ 1)
          1 1
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ r ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ r ∣ 1))
          ℚ.0<1 ℚ.0<1
          (leftMultiplyRationalLipschitzℝ q)
          (leftMultiplyRationalLipschitzℝ r)
          (nonexpandingℝ₂→lipschitzℝ₁ distance distanceNonexpandingℝ₂)
          (nonexpandingℝ₂→lipschitzℝ₂ distance distanceNonexpandingℝ₂)

  π : Continuous g
  π = lipschitz→continuous
        (leftMultiplyRational (ℚ.distance q r) ∘ ∣_∣)
        (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1 ℚ.· 2)
        _
        ρ
    where
    ρ : Lipschitzℝ (leftMultiplyRational (ℚ.distance q r) ∘ ∣_∣)
          (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1 ℚ.· 2) _
    ρ = lipschitzCompose
          (leftMultiplyRational (ℚ.distance q r))
          ∣_∣
          (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1) 2
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1) ℚ.0<1
            (ℚ.≤max' ℚ.∣ ℚ.distance q r ∣ 1))
          ℚ.0<2
          (leftMultiplyRationalLipschitzℝ (ℚ.distance q r))
          magnitudeLipschitzℝ

maxLeftMultiplyRationalNonnegativeₗ :
  (q : ℚ.ℚ)
  (φ : 0 ℚ.≤ q) →
  (x y : ℝ) →
  max (leftMultiplyRational q x) (leftMultiplyRational q y) ≡
  leftMultiplyRational q (max x y)
maxLeftMultiplyRationalNonnegativeₗ q φ =
  continuousExtensionLaw₂ f g f' g' ψ ω χ π ρ σ τ
  where
  f : ℝ → ℝ → ℝ
  f x y = max (leftMultiplyRational q x) (leftMultiplyRational q y)

  g : ℝ → ℝ → ℝ
  g x y = leftMultiplyRational q (max x y)

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' s t = ℚ.max (q ℚ.· s) (q ℚ.· t)

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' s t = q ℚ.· ℚ.max s t

  ψ : (s t : ℚ.ℚ) → f (rational s) (rational t) ≡ rational (f' s t)
  ψ s t = refl

  ω : (s t : ℚ.ℚ) → g (rational s) (rational t) ≡ rational (g' s t)
  ω s t = refl

  χ : (s t : ℚ.ℚ) → f' s t ≡ g' s t
  χ s t = ℚ.maxMultiplyLeftNonnegative q s t φ

  π : (u : ℝ) → Continuous (f u)
  π u = continuousCompose
          (leftMultiplyRational q)
          (max (leftMultiplyRational q u))
          (leftMultiplyRationalContinuous q)
          (maxContinuous₂ (leftMultiplyRational q u))

  ρ : (v : ℝ) → Continuous (flip f v)
  ρ v = continuousCompose
          (leftMultiplyRational q)
          (flip max (leftMultiplyRational q v))
          (leftMultiplyRationalContinuous q)
          (maxContinuous₁ (leftMultiplyRational q v))

  σ : (u : ℝ) → Continuous (g u)
  σ u = continuousCompose
          (max u)
          (leftMultiplyRational q)
          (maxContinuous₂ u)
          (leftMultiplyRationalContinuous q)

  τ : (v : ℝ) → Continuous (flip g v)
  τ v = continuousCompose
          (flip max v)
          (leftMultiplyRational q)
          (maxContinuous₁ v)
          (leftMultiplyRationalContinuous q)

leftMultiplyRationalNonnegativeMonotone :
  (q : ℚ.ℚ)
  (φ : 0 ℚ.≤ q) →
  (x y : ℝ) →
  x ≤ y → leftMultiplyRational q x ≤ leftMultiplyRational q y
leftMultiplyRationalNonnegativeMonotone q φ x y ψ =
  max (leftMultiplyRational q x) (leftMultiplyRational q y)
    ≡⟨ maxLeftMultiplyRationalNonnegativeₗ q φ x y ⟩
  leftMultiplyRational q (max x y)
    ≡⟨ cong (leftMultiplyRational q) ψ ⟩
  leftMultiplyRational q y ∎

leftMultiplyRationalLipschitzℚ₁ :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) →
  ∣ y ∣ ≤ rational L →
  Lipschitzℚ (λ q → leftMultiplyRational q y) L φ
leftMultiplyRationalLipschitzℚ₁ L φ y ψ q r ε ω χ =
  υ
  where
  π : distance (leftMultiplyRational q y) (leftMultiplyRational r y) ≡
      leftMultiplyRational (ℚ.distance q r) ∣ y ∣
  π = distanceLeftMultiplyRational≡leftMultiplyRationalDistanceₗ q r y

  ρ : leftMultiplyRational (ℚ.distance q r) ∣ y ∣ ≤
      leftMultiplyRational (ℚ.distance q r) (rational L)
  ρ = leftMultiplyRationalNonnegativeMonotone
        (ℚ.distance q r)
        (ℚ.0≤∣∣ $ q ℚ.- r)
        ∣ y ∣ (rational L)
        ψ

  σ : (ℚ.distance q r) ℚ.· L ℚ.< ε ℚ.· L
  σ = ℚ.<-·o (ℚ.distance q r) ε L φ χ

  σ' : (ℚ.distance q r) ℚ.· L ℚ.< L ℚ.· ε
  σ' = subst (λ ?x → (ℚ.distance q r) ℚ.· L ℚ.< ?x) (ℚ.·Comm ε L) σ

  τ : leftMultiplyRational (ℚ.distance q r) ∣ y ∣ < rational (L ℚ.· ε)
  τ = ≤→<→< {x = leftMultiplyRational (ℚ.distance q r) ∣ y ∣}
        ρ (rationalStrictMonotone {q = (ℚ.distance q r) ℚ.· L} σ')

  τ' : distance (leftMultiplyRational q y) (leftMultiplyRational r y) <
       rational (L ℚ.· ε)
  τ' = subst (λ ?x → ?x < rational (L ℚ.· ε)) (sym π) τ

  υ : Close (L ℚ.· ε) (ℚ.0<· {x = L} {y = ε} φ ω)
            (leftMultiplyRational q y) (leftMultiplyRational r y)
  υ = distance<→close (ℚ.0<· {x = L} {y = ε} φ ω) τ'

boundedMultiply :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) →
  ∣ y ∣ ≤ rational L →
  ℝ → ℝ
boundedMultiply L φ y ψ =
  liftLipschitz
    (λ q → leftMultiplyRational q y)
    L φ
    (leftMultiplyRationalLipschitzℚ₁ L φ y ψ)

boundedMultiplyLipschitz : 
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) (ψ : ∣ y ∣ ≤ rational L) →
  Lipschitzℝ (boundedMultiply L φ y ψ) L φ
boundedMultiplyLipschitz L φ y ψ =
  liftLipschitzLipschitz
    (λ q → leftMultiplyRational q y)
    L φ
    (leftMultiplyRationalLipschitzℚ₁ L φ y ψ)

boundedMultiplyContinuous :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) (ψ : ∣ y ∣ ≤ rational L) →
  Continuous $ boundedMultiply L φ y ψ
boundedMultiplyContinuous L φ y ψ =
  lipschitz→continuous
    (boundedMultiply L φ y ψ)
    L φ
    (boundedMultiplyLipschitz L φ y ψ)

boundedMultiplyIs2Constant :
  (L₁ L₂ : ℚ.ℚ) (φ₁ : 0 ℚ.< L₁) (φ₂ : 0 ℚ.< L₂)
  (y : ℝ) (ψ₁ : ∣ y ∣ ≤ rational L₁) (ψ₂ : ∣ y ∣ ≤ rational L₂) →
  (x : ℝ) →
  boundedMultiply L₁ φ₁ y ψ₁ x ≡ boundedMultiply L₂ φ₂ y ψ₂ x
boundedMultiplyIs2Constant L₁ L₂ φ₁ φ₂ y ψ₁ ψ₂ =
  continuousExtensionUnique
    (boundedMultiply L₁ φ₁ y ψ₁)
    (boundedMultiply L₂ φ₂ y ψ₂)
    (boundedMultiplyContinuous L₁ φ₁ y ψ₁)
    (boundedMultiplyContinuous L₂ φ₂ y ψ₂)
    (λ q → refl)

boundedMultiplyCurried :
  (x y : ℝ) →
  Σ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q)) → ℝ
boundedMultiplyCurried x y (L , φ , ψ) = boundedMultiply L φ y ψ x

boundedMultiplyCurriedIs2Constant : 
  (x y : ℝ) →
  2-Constant $ boundedMultiplyCurried x y
boundedMultiplyCurriedIs2Constant x y (L , φ , ψ) (M , ω , χ) =
  boundedMultiplyIs2Constant L M φ ω y ψ χ x

_·_ : ℝ → ℝ → ℝ
x · y =
  PropositionalTruncation.SetElim.rec→Set
    ℝ-isSet
    (boundedMultiplyCurried x y)
    (boundedMultiplyCurriedIs2Constant x y)
    φ
  where
  φ : ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q))
  φ = ∣∣≤rational y

infixl 7 _·_

multiply≡boundedMultiply :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L) →
  (x y : ℝ) (ψ : ∣ y ∣ ≤ rational L) →
  x · y ≡ boundedMultiply L φ y ψ x
multiply≡boundedMultiply L φ x y ψ =
  SetElim.helper ℝ-isSet
    (boundedMultiplyCurried x y)
    (boundedMultiplyCurriedIs2Constant x y)
    ω
    χ
  where
  ω : ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q))
  ω = ∣∣≤rational y

  χ : ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q))
  χ = ∣ L , φ , ψ ∣₁

multiply≡boundedMultiply' :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L) →
  (y : ℝ) (ψ : ∣ y ∣ ≤ rational L) →
  (flip _·_ y) ∼ (boundedMultiply L φ y ψ)
multiply≡boundedMultiply' L φ y ψ x = multiply≡boundedMultiply L φ x y ψ

multiply≡boundedMultiply'' :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L) →
  (y : ℝ) (ψ : ∣ y ∣ ≤ rational L) →
  (flip _·_ y) ≡ (boundedMultiply L φ y ψ)
multiply≡boundedMultiply'' L φ y ψ = funExt $ multiply≡boundedMultiply' L φ y ψ

multiplyRational : (q r : ℚ.ℚ) →
  rational q · rational r ≡ rational (q ℚ.· r)
multiplyRational q r = refl

·-leftRational≡leftMultiplyRational :
  (q : ℚ.ℚ) (x : ℝ) →
  rational q · x ≡ leftMultiplyRational q x
·-leftRational≡leftMultiplyRational q x =
  ∃-rec (ℝ-isSet (rational q · x) (leftMultiplyRational q x)) ψ φ
  where
  φ : ∃ ℚ.ℚ (λ q₁ → (0 ℚ.< q₁) × (∣ x ∣ ≤ rational q₁))
  φ = ∣∣≤rational x

  ψ : (L : ℚ.ℚ) →
      (0 ℚ.< L) × (∣ x ∣ ≤ rational L) →
      rational q · x ≡ leftMultiplyRational q x
  ψ L (ω , χ) = rational q · x
                  ≡⟨ multiply≡boundedMultiply L ω (rational q) x χ ⟩
                boundedMultiply L ω x χ (rational q)
                  ≡⟨ refl ⟩
                leftMultiplyRational q x ∎

multiplyLipscthiz₁ :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) (ψ : ∣ y ∣ ≤ rational L) →
  Lipschitzℝ (λ x → x · y) L φ
multiplyLipscthiz₁ L φ y ψ = ω'
  where
  ω : Lipschitzℝ (boundedMultiply L φ y ψ) L φ
  ω = boundedMultiplyLipschitz L φ y ψ

  ω' : Lipschitzℝ (λ x → x · y) L φ
  ω' = subst (λ ?f → Lipschitzℝ ?f L φ)
             (sym $ multiply≡boundedMultiply'' L φ y ψ)
             ω

multiplyContinuous₁ : (y : ℝ) → Continuous $ flip _·_ y
multiplyContinuous₁ y = ∃-rec (continuousProposition $ flip _·_ y) ψ φ
  where
  φ : ∃ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ y ∣ ≤ rational L))
  φ = ∣∣≤rational y

  ψ : (L : ℚ.ℚ) →
      (0 ℚ.< L) × (∣ y ∣ ≤ rational L) →
      Continuous $ flip _·_ y
  ψ L (ω , χ) = lipschitz→continuous
                  (flip _·_ y)
                  L ω
                  (multiplyLipscthiz₁ L ω y χ)

distanceLeftMultiplyRational≡leftMultiplyRationalDistanceᵣ :
  (q : ℚ.ℚ) (x y : ℝ) →
  distance (leftMultiplyRational q x) (leftMultiplyRational q y) ≡
  leftMultiplyRational ℚ.∣ q ∣ (distance x y)
distanceLeftMultiplyRational≡leftMultiplyRationalDistanceᵣ q =
  continuousExtensionLaw₂ f g f' g' φ ψ ω π ρ σ τ
  where
  f : ℝ → ℝ → ℝ
  f x y = distance (leftMultiplyRational q x) (leftMultiplyRational q y)

  g : ℝ → ℝ → ℝ
  g x y = leftMultiplyRational ℚ.∣ q ∣ (distance x y)

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' s t = ℚ.distance (q ℚ.· s) (q ℚ.· t)

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' s t = ℚ.∣ q ∣ ℚ.· ℚ.distance s t

  φ : (s t : ℚ.ℚ) → f (rational s) (rational t) ≡ rational (f' s t)
  φ s t = refl

  ψ : (s t : ℚ.ℚ) → g (rational s) (rational t) ≡ rational (g' s t)
  ψ s t = refl

  ω : (s t : ℚ.ℚ) → f' s t ≡ g' s t
  ω s t = ℚ.·distanceₗ q s t

  π : (u : ℝ) → Continuous (f u)
  π u = continuousCompose
          (leftMultiplyRational q)
          (distance (leftMultiplyRational q u))
          (leftMultiplyRationalContinuous q)
          (distanceContinuous₂ (leftMultiplyRational q u))

  ρ : (v : ℝ) → Continuous (flip f v)
  ρ v = continuousCompose
          (leftMultiplyRational q)
          (flip distance (leftMultiplyRational q v))
          (leftMultiplyRationalContinuous q)
          (distanceContinuous₁ (leftMultiplyRational q v))

  σ : (u : ℝ) → Continuous (g u)
  σ u = continuousCompose
          (distance u)
          (leftMultiplyRational ℚ.∣ q ∣)
          (distanceContinuous₂ u)
          (leftMultiplyRationalContinuous ℚ.∣ q ∣)

  τ : (v : ℝ) → Continuous (flip g v)
  τ v = continuousCompose
          (flip distance v)
          (leftMultiplyRational ℚ.∣ q ∣)
          (distanceContinuous₁ v)
          (leftMultiplyRationalContinuous ℚ.∣ q ∣)

·distanceₗ : (a x y : ℝ) →
            distance (a · x) (a · y) ≡ ∣ a ∣ · distance x y
·distanceₗ a x y =
  continuousExtensionUnique f g χ π ω a
  where
  f : ℝ → ℝ
  f a = distance (a · x) (a · y)

  g : ℝ → ℝ
  g a = ∣ a ∣ · distance x y

  χ : Continuous f
  χ = γ
    where
    α : ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ x ∣ ≤ rational q))
    α = ∣∣≤rational x

    β : ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q))
    β = ∣∣≤rational y

    γ : Continuous f
    γ = PropositionalTruncation.rec2 (continuousProposition f) γ' α β
      where
      γ' : Σ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ x ∣ ≤ rational L)) →
           Σ ℚ.ℚ (λ M → (0 ℚ.< M) × (∣ y ∣ ≤ rational M)) →
           Continuous f
      γ' (L , ζ , ι) (M , ζ' , ι') = ν
        where
        ζ'' : 0 ℚ.< 1 ℚ.· L ℚ.+ 1 ℚ.· M
        ζ'' = ℚ.0<+' {x = 1 ℚ.· L} {y = 1 ℚ.· M}
                     (ℚ.0<· {x = 1} {y = L} ℚ.0<1 ζ)
                     (ℚ.0<· {x = 1} {y = M} ℚ.0<1 ζ')

        κ₁ : Lipschitzℝ (flip _·_ x) L ζ
        κ₁ = multiplyLipscthiz₁ L ζ x ι

        κ₂ : Lipschitzℝ (flip _·_ y) M ζ'
        κ₂ = multiplyLipscthiz₁ M ζ' y ι'

        μ : Lipschitzℝ f (1 ℚ.· L ℚ.+ 1 ℚ.· M) ζ''
        μ = lipschitz₂-composeLipschitz₁-lipschitz
              L M 1 1 ζ ζ' ℚ.0<1 ℚ.0<1 κ₁ κ₂
              distanceLipschitz₁
              distanceLipschitz₂

        ν : Continuous f
        ν = lipschitz→continuous f (1 ℚ.· L ℚ.+ 1 ℚ.· M) ζ'' μ

  π : Continuous g
  π = continuousCompose
        ∣_∣
        (flip _·_ (distance x y))
        magnitudeContinuous
        (multiplyContinuous₁ (distance x y))

  ω : (f ∘ rational) ∼ (g ∘ rational)
  ω q =
    distance (rational q · x) (rational q · y)
      ≡⟨ cong₂ distance (·-leftRational≡leftMultiplyRational q x)
                         (·-leftRational≡leftMultiplyRational q y) ⟩
    distance (leftMultiplyRational q x) (leftMultiplyRational q y)
      ≡⟨ distanceLeftMultiplyRational≡leftMultiplyRationalDistanceᵣ q x y ⟩
    leftMultiplyRational ℚ.∣ q ∣ (distance x y)
      ≡⟨ sym (·-leftRational≡leftMultiplyRational ℚ.∣ q ∣ (distance x y)) ⟩
    rational ℚ.∣ q ∣ · distance x y
      ≡⟨ cong (flip _·_ (distance x y))
              (sym (magnitudeRational q)) ⟩
    ∣ rational q ∣ · distance x y ∎

maxMultiplyLeftMagnitude : (a x y : ℝ) →
  max (∣ a ∣ · x) (∣ a ∣ · y) ≡ ∣ a ∣ · max x y
maxMultiplyLeftMagnitude a x y =
  continuousExtensionUnique f g φ ψ ω a
  where
  f : ℝ → ℝ
  f a = max (∣ a ∣ · x) (∣ a ∣ · y)

  g : ℝ → ℝ
  g a = ∣ a ∣ · max x y

  φ : Continuous f
  φ = continuousCompose ∣_∣ h magnitudeContinuous φ'
    where
    h : ℝ → ℝ
    h b = max (b · x) (b · y)

    φ' : Continuous h
    φ' = PropositionalTruncation.rec2 (continuousProposition h) γ' α β
      where
      α : ∃ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ x ∣ ≤ rational L))
      α = ∣∣≤rational x
  
      β : ∃ ℚ.ℚ (λ M → (0 ℚ.< M) × (∣ y ∣ ≤ rational M))
      β = ∣∣≤rational y

      γ' : Σ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ x ∣ ≤ rational L)) →
           Σ ℚ.ℚ (λ M → (0 ℚ.< M) × (∣ y ∣ ≤ rational M)) →
           Continuous h
      γ' (L , ζ , ι) (M , ζ' , ι') = ν
        where
        ζ'' : 0 ℚ.< 1 ℚ.· L ℚ.+ 1 ℚ.· M
        ζ'' = ℚ.0<+' {x = 1 ℚ.· L} {y = 1 ℚ.· M}
                     (ℚ.0<· {x = 1} {y = L} ℚ.0<1 ζ)
                     (ℚ.0<· {x = 1} {y = M} ℚ.0<1 ζ')

        κ₁ : Lipschitzℝ (flip _·_ x) L ζ
        κ₁ = multiplyLipscthiz₁ L ζ x ι

        κ₂ : Lipschitzℝ (flip _·_ y) M ζ'
        κ₂ = multiplyLipscthiz₁ M ζ' y ι'

        μ : Lipschitzℝ h (1 ℚ.· L ℚ.+ 1 ℚ.· M) ζ''
        μ = lipschitz₂-composeLipschitz₁-lipschitz
              L M 1 1 ζ ζ' ℚ.0<1 ℚ.0<1
              κ₁ κ₂ maxLipschitz₁ maxLipschitz₂

        ν : Continuous h
        ν = lipschitz→continuous h (1 ℚ.· L ℚ.+ 1 ℚ.· M) ζ'' μ

  ψ : Continuous g
  ψ = continuousCompose
        ∣_∣ (flip _·_ (max x y))
        magnitudeContinuous (multiplyContinuous₁ (max x y))

  ω : (f ∘ rational) ∼ (g ∘ rational)
  ω q =
    max (∣ rational q ∣ · x) (∣ rational q ∣ · y)
      ≡⟨ cong (λ c → max (c · x) (c · y))
              (magnitudeRational q) ⟩
    max (rational ℚ.∣ q ∣ · x) (rational ℚ.∣ q ∣ · y)
      ≡⟨ cong₂ max (·-leftRational≡leftMultiplyRational ℚ.∣ q ∣ x)
                     (·-leftRational≡leftMultiplyRational ℚ.∣ q ∣ y) ⟩
    max (leftMultiplyRational ℚ.∣ q ∣ x) (leftMultiplyRational ℚ.∣ q ∣ y)
      ≡⟨ maxLeftMultiplyRationalNonnegativeₗ ℚ.∣ q ∣ (ℚ.0≤∣∣ q) x y ⟩
    leftMultiplyRational ℚ.∣ q ∣ (max x y)
      ≡⟨ sym (·-leftRational≡leftMultiplyRational ℚ.∣ q ∣ (max x y)) ⟩
    rational ℚ.∣ q ∣ · max x y
      ≡⟨ cong (flip _·_ (max x y))
              (sym (magnitudeRational q)) ⟩
    ∣ rational q ∣ · max x y ∎

maxLeftMultiplyRationalᵣ :
  (a : ℝ)
  (q r : ℚ.ℚ) →
  max (leftMultiplyRational q ∣ a ∣) (leftMultiplyRational r ∣ a ∣) ≡
  leftMultiplyRational (ℚ.max q r) ∣ a ∣
maxLeftMultiplyRationalᵣ a q r =
  continuousExtensionUnique f g φ ψ ω a
  where
  f : ℝ → ℝ
  f a = max (leftMultiplyRational q ∣ a ∣) (leftMultiplyRational r ∣ a ∣)

  g : ℝ → ℝ
  g a = leftMultiplyRational (ℚ.max q r) ∣ a ∣

  φ : Continuous f
  φ = continuousCompose ∣_∣ h magnitudeContinuous φ'
    where
    h : ℝ → ℝ
    h b = max (leftMultiplyRational q b) (leftMultiplyRational r b)

    φ' : Continuous h
    φ' = lipschitz→continuous
           h (1 ℚ.· ℚ.max ℚ.∣ q ∣ 1 ℚ.+ 1 ℚ.· ℚ.max ℚ.∣ r ∣ 1) _ φ''
      where
      φ'' : Lipschitzℝ
             h
             (1 ℚ.· ℚ.max ℚ.∣ q ∣ 1 ℚ.+ 1 ℚ.· ℚ.max ℚ.∣ r ∣ 1)
             _
      φ'' = lipschitz₂-composeLipschitz₁-lipschitz
              (ℚ.max ℚ.∣ q ∣ 1) (ℚ.max ℚ.∣ r ∣ 1) 1 1
              (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
              (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ r ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ r ∣ 1))
              ℚ.0<1 ℚ.0<1
              (leftMultiplyRationalLipschitzℝ q)
              (leftMultiplyRationalLipschitzℝ r)
              maxLipschitz₁
              maxLipschitz₂

  ψ : Continuous g
  ψ = lipschitz→continuous g (ℚ.max ℚ.∣ ℚ.max q r ∣ 1 ℚ.· 2) _ ψ'
    where
    ψ' : Lipschitzℝ g (ℚ.max ℚ.∣ ℚ.max q r ∣ 1 ℚ.· 2) _
    ψ' = lipschitzCompose
          (leftMultiplyRational (ℚ.max q r))
          ∣_∣
          (ℚ.max ℚ.∣ ℚ.max q r ∣ 1) 2
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ ℚ.max q r ∣ 1)
            ℚ.0<1 (ℚ.≤max' ℚ.∣ ℚ.max q r ∣ 1))
          ℚ.0<2
          (leftMultiplyRationalLipschitzℝ (ℚ.max q r))
          magnitudeLipschitzℝ

  ω : (f ∘ rational) ∼ (g ∘ rational)
  ω s =
    max (leftMultiplyRational q ∣ rational s ∣)
        (leftMultiplyRational r ∣ rational s ∣)
      ≡⟨ cong (λ c → max (leftMultiplyRational q c) (leftMultiplyRational r c))
              (magnitudeRational s) ⟩
    max (rational (q ℚ.· ℚ.∣ s ∣)) (rational (r ℚ.· ℚ.∣ s ∣))
      ≡⟨ liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂
           (q ℚ.· ℚ.∣ s ∣) (r ℚ.· ℚ.∣ s ∣) ⟩
    rational (ℚ.max (q ℚ.· ℚ.∣ s ∣) (r ℚ.· ℚ.∣ s ∣))
      ≡⟨ cong rational
              (ℚ.maxMultiplyRightNonnegative ℚ.∣ s ∣ q r (ℚ.0≤∣∣ s)
               ∙ ℚ.·Comm ℚ.∣ s ∣ (ℚ.max q r)) ⟩
    rational (ℚ.max q r ℚ.· ℚ.∣ s ∣)
      ≡⟨ cong (leftMultiplyRational (ℚ.max q r))
              (sym (magnitudeRational s)) ⟩
    leftMultiplyRational (ℚ.max q r) ∣ rational s ∣ ∎

maxMultiplyRightMagnitude : (a x y : ℝ) →
  max (x · ∣ a ∣) (y · ∣ a ∣) ≡ max x y · ∣ a ∣
maxMultiplyRightMagnitude a =
  continuousExtensionUnique₂ f g φ ψ ω χ π
  where
  f : ℝ → ℝ → ℝ
  f x y = max (x · ∣ a ∣) (y · ∣ a ∣)

  g : ℝ → ℝ → ℝ
  g x y = max x y · ∣ a ∣

  φ : (x : ℝ) → Continuous $ f x
  φ x = continuousCompose
          (flip _·_ $ ∣ a ∣) (max (x · ∣ a ∣))
          (multiplyContinuous₁ ∣ a ∣) (maxContinuous₂ $ x · ∣ a ∣)

  ψ : (x : ℝ) → Continuous $ g x
  ψ x = continuousCompose
          (max x) (flip _·_ ∣ a ∣)
          (maxContinuous₂ x) (multiplyContinuous₁ ∣ a ∣)

  ω : (y : ℝ) → Continuous $ flip f y
  ω y = continuousCompose
          (flip _·_ ∣ a ∣) (flip max $ y · ∣ a ∣)
          (multiplyContinuous₁ ∣ a ∣) (maxContinuous₁ $ y · ∣ a ∣)

  χ : (y : ℝ) → Continuous $ flip g y
  χ y = continuousCompose
          (flip max y) (flip _·_ ∣ a ∣)
          (maxContinuous₁ y) (multiplyContinuous₁ ∣ a ∣)

  π : (q r : ℚ.ℚ) →
      f (rational q) (rational r) ≡ g (rational q) (rational r)
  π q r = max (rational q · ∣ a ∣) (rational r · ∣ a ∣)
            ≡⟨ cong₂ max (·-leftRational≡leftMultiplyRational q ∣ a ∣)
                         (·-leftRational≡leftMultiplyRational r ∣ a ∣) ⟩
          max (leftMultiplyRational q ∣ a ∣) (leftMultiplyRational r ∣ a ∣)
            ≡⟨ maxLeftMultiplyRationalᵣ a q r ⟩
          leftMultiplyRational (ℚ.max q r) ∣ a ∣
            ≡⟨ (sym $ ·-leftRational≡leftMultiplyRational (ℚ.max q r) ∣ a ∣) ⟩
          rational (ℚ.max q r) · ∣ a ∣
            ≡⟨ refl ⟩
          max (rational q) (rational r) · ∣ a ∣ ∎

multiplyMagnitudeLeftMonotone : (a x y : ℝ) →
  x ≤ y → ∣ a ∣ · x ≤ ∣ a ∣ · y
multiplyMagnitudeLeftMonotone a x y φ =
  max (∣ a ∣ · x) (∣ a ∣ · y)
    ≡⟨ maxMultiplyLeftMagnitude a x y ⟩
  ∣ a ∣ · max x y
    ≡⟨ cong (_·_ $ ∣ a ∣) φ ⟩
  ∣ a ∣ · y ∎

multiplyMagnitudeRightMonotone : (a x y : ℝ) →
  x ≤ y → x · ∣ a ∣ ≤ y · ∣ a ∣
multiplyMagnitudeRightMonotone a x y φ =
  max (x · ∣ a ∣) (y · ∣ a ∣)
    ≡⟨ maxMultiplyRightMagnitude a x y ⟩
  max x y · ∣ a ∣
    ≡⟨ cong (flip _·_ $ ∣ a ∣) φ ⟩
  y · ∣ a ∣ ∎

multiplyNonnegativeLeftMonotone : (a x y : ℝ) →
  0 ≤ a →
  x ≤ y → a · x ≤ a · y
multiplyNonnegativeLeftMonotone a x y φ ψ = ω'
  where
  ω : ∣ a ∣ · x ≤ ∣ a ∣ · y
  ω = multiplyMagnitudeLeftMonotone a x y ψ

  ω' : a · x ≤ a · y
  ω' = subst (λ ?a → ?a · x ≤ ?a · y) (0≤→∣∣≡self a φ) ω

multiplyNonnegativeRightMonotone : (a x y : ℝ) →
  0 ≤ a →
  x ≤ y → x · a ≤ y · a
multiplyNonnegativeRightMonotone a x y φ ψ = ω'
  where
  ω : x · ∣ a ∣ ≤ y · ∣ a ∣
  ω = multiplyMagnitudeRightMonotone a x y ψ

  ω' : x · a ≤ y · a
  ω' = subst (λ ?a → x · ?a ≤ y · ?a) (0≤→∣∣≡self a φ) ω

·≤· : {x y z w : ℝ} →
  x ≤ z → y ≤ w →
  0 ≤ z → 0 ≤ y →
  x · y ≤ z · w
·≤· {x} {y} {z} {w} p q r s =
  ≤-transitive
    (x · y) (z · y) (z · w)
    (multiplyNonnegativeRightMonotone y x z s p)
    (multiplyNonnegativeLeftMonotone z y w r q)

multiplyContinuous₂ : (x : ℝ) → Continuous $ _·_ x
multiplyContinuous₂ x y ε φ = ω
  where
  ψ : ∃ ℚ.ℚ (λ η → (0 ℚ.< η) × (∣ x ∣ ≤ rational η))
  ψ = ∣∣≤rational x

  ω : ∃ ℚ.ℚ
      (λ δ →
      Σ (0 ℚ.< δ)
      (λ ζ → (z : ℝ) → Close δ ζ y z → Close ε φ (x · y) (x · z)))
  ω = PropositionalTruncation.map ω' ψ
    where
    ω' : Σ ℚ.ℚ (λ η → (0 ℚ.< η) × (∣ x ∣ ≤ rational η)) →
         Σ ℚ.ℚ
         (λ δ →
         Σ (0 ℚ.< δ)
         (λ ζ → (z : ℝ) → Close δ ζ y z → Close ε φ (x · y) (x · z)))
    ω' (η , χ , π) = δ , (σ , τ)
      where
      χ' : ¬ η ≡ 0
      χ' = ≠-symmetric $ ℚ.<→≠ χ

      δ : ℚ.ℚ
      δ = η [ χ' ]⁻¹ ℚ.· (ε / 2 [ ℚ.2≠0 ])

      σ : 0 ℚ.< δ
      σ = ℚ.0<· {x = η [ χ' ]⁻¹} {y = ε / 2 [ ℚ.2≠0 ]}
                (ℚ.0<⁻¹' {x = η} χ) (ℚ.0</' {x = ε} {y = 2} φ ℚ.0<2)

      τ : (z : ℝ) → Close δ σ y z → Close ε φ (x · y) (x · z)
      τ z υ = β'
        where
        υ' : distance y z < rational δ
        υ' = close→distance< σ υ

        ξ : distance (x · y) (x · z) ≡ ∣ x ∣ · distance y z
        ξ = ·distanceₗ x y z

        ο : ∣ x ∣ · distance y z ≤ rational (η ℚ.· δ)
        ο = ·≤· {x = ∣ x ∣} {y = distance y z}
                {z = rational η} {w = rational δ}
                π
                (<→≤ {x = distance y z} {y = rational δ} υ')
                (<→≤ {x = 0} $ rationalStrictMonotone {q = 0} {r = η} χ)
                (0≤distance y z) 

        α : η ℚ.· δ ≡ ε / 2 [ ℚ.2≠0 ]
        α = η ℚ.· (η [ χ' ]⁻¹ ℚ.· (ε / 2 [ ℚ.2≠0 ]))
              ≡⟨ ℚ.·Assoc η (η [ χ' ]⁻¹) (ε / 2 [ ℚ.2≠0 ]) ⟩
            (η ℚ.· η [ χ' ]⁻¹) ℚ.· (ε / 2 [ ℚ.2≠0 ])
              ≡⟨ cong (λ z → z ℚ.· (ε / 2 [ ℚ.2≠0 ])) (ℚ.⁻¹-inverse η χ') ⟩
            1 ℚ.· (ε / 2 [ ℚ.2≠0 ])
              ≡⟨ (ℚ.·IdL $ (ε / 2 [ ℚ.2≠0 ])) ⟩
            ε / 2 [ ℚ.2≠0 ] ∎

        ο' : distance (x · y) (x · z) ≤ rational (ε / 2 [ ℚ.2≠0 ])
        ο' = subst2 _≤_ (sym ξ) (cong rational α) ο

        β : distance (x · y) (x · z) < rational ε
        β = ≤→<→< {x = distance (x · y) (x · z)}
                  ο'
                  (rationalStrictMonotone {q = ε / 2 [ ℚ.2≠0 ]} $
                   ℚ.self/2<self ε φ)

        β' : Close ε φ (x · y) (x · z)
        β' = distance<→close φ β

·-commutative : (x y : ℝ) → x · y ≡ y · x
·-commutative =
  continuousExtensionLaw₂
    _·_ (flip _·_) ℚ._·_ (flip ℚ._·_)
    φ (flip φ) ψ ω χ χ ω
  where
  φ : (q r : ℚ.ℚ) → rational q · rational r ≡ rational (q ℚ.· r)
  φ q r = refl

  ψ : (q r : ℚ.ℚ) → q ℚ.· r ≡ r ℚ.· q
  ψ = ℚ.·Comm

  ω : (u : ℝ) → Continuous (_·_ u)
  ω = multiplyContinuous₂

  χ : (v : ℝ) → Continuous $ flip _·_ v
  χ = multiplyContinuous₁

·-associative : (x y z : ℝ) → (x · y) · z ≡ x · (y · z)
·-associative =
  continuousExtensionLaw₃
    associateℝₗ
    associateℝᵣ
    associateℚₗ
    associateℚᵣ
    ψ ω χ π ρ σ τ υ ξ
  where
  associateℝₗ : ℝ → ℝ → ℝ → ℝ
  associateℝₗ x y z = (x · y) · z

  associateℝᵣ : ℝ → ℝ → ℝ → ℝ
  associateℝᵣ x y z = x · (y · z)

  associateℚₗ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚₗ x y z = (x ℚ.· y) ℚ.· z

  associateℚᵣ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚᵣ x y z = x ℚ.· (y ℚ.· z)

  ψ : (q r s : ℚ.ℚ) →
      associateℝₗ (rational q) (rational r) (rational s) ≡
      rational (associateℚₗ q r s)
  ψ q r s = refl

  ω : (q r s : ℚ.ℚ) →
      associateℝᵣ (rational q) (rational r) (rational s) ≡
      rational (associateℚᵣ q r s)
  ω q r s = refl

  χ : (q r s : ℚ.ℚ) → associateℚₗ q r s ≡ associateℚᵣ q r s
  χ q r s = sym $ ℚ.·Assoc q r s

  π : (x y : ℝ) → Continuous (associateℝₗ x y)
  π x y = multiplyContinuous₂ (x · y)

  ρ : (x z : ℝ) → Continuous (λ y → associateℝₗ x y z)
  ρ x z = continuousCompose (_·_ x) (flip _·_ z)
                            (multiplyContinuous₂ x) (multiplyContinuous₁ z)

  σ : (y z : ℝ) → Continuous (λ x → associateℝₗ x y z)
  σ y z = continuousCompose (flip _·_ y) (flip _·_ z)
                            (multiplyContinuous₁ y) (multiplyContinuous₁ z)

  τ : (x y : ℝ) → Continuous (associateℝᵣ x y)
  τ x y = continuousCompose (_·_ y) (_·_ x)
                            (multiplyContinuous₂ y) (multiplyContinuous₂ x)

  υ : (x z : ℝ) → Continuous (λ y → associateℝᵣ x y z)
  υ x z = continuousCompose (flip _·_ z) (_·_ x)
                            (multiplyContinuous₁ z) (multiplyContinuous₂ x)

  ξ : (y z : ℝ) → Continuous (λ x → associateℝᵣ x y z)
  ξ y z = multiplyContinuous₁ (y · z)

·-associative' : (x y z : ℝ) → x · (y · z) ≡ (x · y) · z
·-associative' x y z = sym $ ·-associative x y z

·-unitˡ : (x : ℝ) → 1 · x ≡ x
·-unitˡ =
  continuousExtensionLaw₁
    (_·_ 1) (idfun ℝ)
    (ℚ._·_ 1) (idfun ℚ.ℚ)
    H K L φ ψ
  where
  H : (_·_ 1 ∘ rational) ∼ (rational ∘ ℚ._·_ 1)
  H q = refl

  K : (idfun ℝ ∘ rational) ∼ (rational ∘ idfun ℚ.ℚ)
  K q = refl

  L : ℚ._·_ 1 ∼ idfun ℚ.ℚ
  L = ℚ.·IdL

  φ : Continuous (_·_ 1)
  φ = multiplyContinuous₂ 1

  ψ : Continuous (idfun ℝ)
  ψ = identityContinuous

·-unitʳ : (x : ℝ) → x · 1 ≡ x
·-unitʳ x =
  let
    -- Agda, why are you like this?
    φ = ·-commutative x 1

    ψ : 1 · x ≡ x
    ψ = ·-unitˡ x
  in φ ∙ ψ

·-distributesOver-+ˡ : (x y z : ℝ) → x · (y + z) ≡ x · y + x · z
·-distributesOver-+ˡ =
  continuousExtensionLaw₃
    f g f' g'
    ψ ω χ π ρ σ τ υ ξ
  where
  φ₊ : (q r : ℚ.ℚ) →
      _+_ (rational q) (rational r) ≡ rational (q ℚ.+ r)
  φ₊ = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

  f : ℝ → ℝ → ℝ → ℝ
  f x y z = x · (y + z)

  g : ℝ → ℝ → ℝ → ℝ
  g x y z = x · y + x · z

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' q r s = q ℚ.· (r ℚ.+ s)

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' q r s = q ℚ.· r ℚ.+ q ℚ.· s

  ψ : (q r s : ℚ.ℚ) →
      f (rational q) (rational r) (rational s) ≡
      rational (f' q r s)
  ψ q r s = cong (_·_ (rational q)) (φ₊ r s)

  ω : (q r s : ℚ.ℚ) →
      g (rational q) (rational r) (rational s) ≡
      rational (g' q r s)
  ω q r s = φ₊ (q ℚ.· r) (q ℚ.· s)

  χ : (q r s : ℚ.ℚ) → f' q r s ≡ g' q r s
  χ = ℚ.·DistL+

  π : (x y : ℝ) → Continuous (λ z → f x y z)
  π x y = continuousCompose (_+_ y) (_·_ x)
                            (+continuous₂ y) (multiplyContinuous₂ x)

  ρ : (x z : ℝ) → Continuous (λ y → f x y z)
  ρ x z = continuousCompose (flip _+_ z) (_·_ x)
                            (+continuous₁ z) (multiplyContinuous₂ x)

  σ : (y z : ℝ) → Continuous (λ x → f x y z)
  σ y z = multiplyContinuous₁ (y + z)

  τ : (x y : ℝ) → Continuous (λ z → g x y z)
  τ x y = continuousCompose (_·_ x) (_+_ (x · y))
                            (multiplyContinuous₂ x) (+continuous₂ (x · y))

  υ : (x z : ℝ) → Continuous (λ y → g x y z)
  υ x z = continuousCompose (_·_ x) (flip _+_ (x · z))
                            (multiplyContinuous₂ x) (+continuous₁ (x · z))

  ξ : (y z : ℝ) → Continuous (λ x → g x y z)
  ξ y z = PropositionalTruncation.rec2
            (continuousProposition (λ x → x · y + x · z)) γ α β
    where
    α : ∃ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ y ∣ ≤ rational L))
    α = ∣∣≤rational y

    β : ∃ ℚ.ℚ (λ M → (0 ℚ.< M) × (∣ z ∣ ≤ rational M))
    β = ∣∣≤rational z

    γ : Σ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ y ∣ ≤ rational L)) →
        Σ ℚ.ℚ (λ M → (0 ℚ.< M) × (∣ z ∣ ≤ rational M)) →
        Continuous (λ x → x · y + x · z)
    γ (L , ζ , ι) (M , ζ' , ι') = ν
      where
      ζ'' : 0 ℚ.< 1 ℚ.· L ℚ.+ 1 ℚ.· M
      ζ'' = ℚ.0<+' {x = 1 ℚ.· L} {y = 1 ℚ.· M}
                   (ℚ.0<· {x = 1} {y = L} ℚ.0<1 ζ)
                   (ℚ.0<· {x = 1} {y = M} ℚ.0<1 ζ')

      μ : Lipschitzℝ (λ x → x · y + x · z) (1 ℚ.· L ℚ.+ 1 ℚ.· M) ζ''
      μ = lipschitz₂-composeLipschitz₁-lipschitz
            L M 1 1 ζ ζ' ℚ.0<1 ℚ.0<1
            (multiplyLipscthiz₁ L ζ y ι)
            (multiplyLipscthiz₁ M ζ' z ι')
            +lipschitz₁ +lipschitz₂

      ν : Continuous (λ x → x · y + x · z)
      ν = lipschitz→continuous
            (λ x → x · y + x · z) (1 ℚ.· L ℚ.+ 1 ℚ.· M) ζ'' μ

·-distributesOver-+ʳ : (x y z : ℝ) → (y + z) · x ≡ y · x + z · x
·-distributesOver-+ʳ x y z =
  (y + z) · x
    ≡⟨ ·-commutative (y + z) x ⟩
  x · (y + z)
    ≡⟨ ·-distributesOver-+ˡ x y z ⟩
  x · y + x · z
    ≡⟨ cong₂ _+_ (·-commutative x y) (·-commutative x z) ⟩
  y · x + z · x ∎

isCommutativeRingℝ : IsCommRing 0 1 _+_ _·_ (-_)
isCommutativeRingℝ =
  makeIsCommRing
    ℝ-isSet
    +-associative'
    +-unitʳ
    +-inverseᵣ
    +-commutative
    ·-associative'
    ·-unitʳ
    ·-distributesOver-+ˡ
    ·-commutative

ℝCommutativeRing : CommRing ℓ-zero
ℝCommutativeRing = ℝ , (commringstr 0 1 _+_ _·_ -_ isCommutativeRingℝ)

ℝRing : Ring ℓ-zero
ℝRing = CommRing→Ring ℝCommutativeRing

isRingℝ : IsRing 0 1 _+_ _·_ (-_)
isRingℝ = IsCommRing.isRing isCommutativeRingℝ

multiplyLipscthiz₂ :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (x : ℝ) (ψ : ∣ x ∣ ≤ rational L) →
  Lipschitzℝ (λ y → x · y) L φ
multiplyLipscthiz₂ L φ x ψ = ω'
  where
  ω : Lipschitzℝ (λ y → y · x) L φ
  ω = multiplyLipscthiz₁ L φ x ψ

  ω' : Lipschitzℝ (λ y → x · y) L φ
  ω' = subst (λ ?f → Lipschitzℝ ?f L φ) (funExt (flip ·-commutative x)) ω

multiplyNegateLeft :
  (x y : ℝ) → (- x) · y ≡ - (x · y)
multiplyNegateLeft =
  continuousExtensionLaw₂ f g f' g' H K L φ ψ ω χ
  where
  f : ℝ → ℝ → ℝ
  f x y = (- x) · y

  g : ℝ → ℝ → ℝ
  g x y = - (x · y)

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' q r = (ℚ.- q) ℚ.· r

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' q r = ℚ.- (q ℚ.· r)

  H : (q r : ℚ.ℚ) → f (rational q) (rational r) ≡ rational (f' q r)
  H q r = cong (flip _·_ (rational r)) (-rational q)

  K : (q r : ℚ.ℚ) → g (rational q) (rational r) ≡ rational (g' q r)
  K q r = -rational (q ℚ.· r)

  L : (q r : ℚ.ℚ) → f' q r ≡ g' q r
  L q r = sym (ℚ.-·≡-· q r)

  φ : (u : ℝ) → Continuous (f u)
  φ u = multiplyContinuous₂ (- u)

  ψ : (v : ℝ) → Continuous (flip f v)
  ψ v = continuousCompose -_ (flip _·_ v) -continuous (multiplyContinuous₁ v)

  ω : (u : ℝ) → Continuous (g u)
  ω u = continuousCompose (_·_ u) -_ (multiplyContinuous₂ u) -continuous

  χ : (v : ℝ) → Continuous (flip g v)
  χ v = continuousCompose (flip _·_ v) -_ (multiplyContinuous₁ v) -continuous

multiplyNegateRight :
  (x y : ℝ) → x · (- y) ≡ - (x · y)
multiplyNegateRight x y =
  x · (- y)
    ≡⟨ ·-commutative x (- y) ⟩
  (- y) · x
    ≡⟨ multiplyNegateLeft y x ⟩
  - (y · x)
    ≡⟨ cong -_ (·-commutative y x) ⟩
  - (x · y) ∎
