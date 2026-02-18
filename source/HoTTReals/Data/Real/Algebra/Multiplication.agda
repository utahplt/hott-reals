module HoTTReals.Data.Real.Algebra.Multiplication where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Nat.Literals public
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Real.Algebra.Negation
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

distanceLeftMultiplyRational≡leftMultiplyRationalDistance :
  (q r : ℚ.ℚ)
  (y : ℝ) →
  distance (leftMultiplyRational q y) (leftMultiplyRational r y) ≡
  leftMultiplyRational (ℚ.distance q r) ∣ y ∣
distanceLeftMultiplyRational≡leftMultiplyRationalDistance q r =
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

maxLeftMultiplyRationalNonnegative :
  (q : ℚ.ℚ)
  (φ : 0 ℚ.≤ q) →
  (x y : ℝ) →
  max (leftMultiplyRational q x) (leftMultiplyRational q y) ≡
  leftMultiplyRational q (max x y)
maxLeftMultiplyRationalNonnegative q φ =
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
    ≡⟨ maxLeftMultiplyRationalNonnegative q φ x y ⟩
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
  π = distanceLeftMultiplyRational≡leftMultiplyRationalDistance q r y

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

_·_ : ℝ → ℝ → ℝ
x · y = PropositionalTruncation.SetElim.rec→Set ℝ-isSet
           -- (λ (a₁ , φ₁ , ψ₁) (a₂ , φ₂ , ψ₂) → ...)  -- 2-Constant proof
           (λ (a , φ , ψ) → boundedMultiply a φ y ψ x)
           {!!}
           (∣∣≤rational y)

infixl 7 _·_
