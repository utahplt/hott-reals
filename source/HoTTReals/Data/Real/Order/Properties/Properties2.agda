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

module ApproximateBelow
  (x : ℝ) 
  where

  approximateBelow : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ
  approximateBelow ε φ = x - rational ε

  approximateBelowCauchy :
    CauchyApproximation approximateBelow
  approximateBelowCauchy ε δ φ ψ = χ'''
    where
    ω : ∣ (x - rational ε) - (x - rational δ) ∣ ≡ rational ℚ.∣ ε ℚ.- δ ∣
    ω = ∣ (x - rational ε) - (x - rational δ) ∣
          ≡⟨ cong (λ ?x → ∣ (x - rational ε) + ?x ∣)
                  (negateSubtract x (rational δ)) ⟩
        ∣ (x - rational ε) + (- x + rational δ) ∣
          ≡⟨ (cong ∣_∣ $ sym $ +-associative (x - rational ε)
                                             (- x)
                                             (rational δ)) ⟩
        ∣ ((x - rational ε) + - x) + rational δ ∣
          ≡⟨ cong (λ ?x → ∣ ?x + rational δ ∣)
                  (addSubtractLeftCancel x (- rational ε)) ⟩
        ∣ - rational ε + rational δ ∣
          ≡⟨ (cong ∣_∣ $ +-commutative (- rational ε) (rational δ)) ⟩
        ∣ rational δ - rational ε ∣
          ≡⟨ distanceCommutative (rational δ) (rational ε) ⟩
        ∣ rational ε - rational δ ∣
          ≡⟨ cong ∣_∣ (+rational ε (ℚ.- δ)) ⟩
        ∣ rational (ε ℚ.- δ) ∣
          ≡⟨ magnitudeRational (ε ℚ.- δ) ⟩
        rational ℚ.∣ ε ℚ.- δ ∣ ∎
  
    χ : ℚ.∣ ε ℚ.- δ ∣ ℚ.< ε ℚ.+ δ
    χ = ℚ.0<→distance<+ {ε} {δ} φ ψ
  
    χ' : rational ℚ.∣ ε ℚ.- δ ∣ < rational (ε ℚ.+ δ)
    χ' = rationalStrictMonotone {ℚ.∣ ε ℚ.- δ ∣} {ε ℚ.+ δ} χ
  
    χ'' : ∣ (x - rational ε) - (x - rational δ) ∣ < rational (ε ℚ.+ δ)
    χ'' = subst (flip _<_ $ rational (ε ℚ.+ δ)) (sym ω) χ'
  
    χ''' : Close (ε ℚ.+ δ) (ℚ.0<+' {ε} {δ} φ ψ)
                 (x - rational ε) (x - rational δ)
    χ''' = distance<→close _ χ''

  approximateBelowLimit :
    limit approximateBelow approximateBelowCauchy ≡ x
  approximateBelowLimit =
    path (limit approximateBelow approximateBelowCauchy) x φ
    where
    φ : (ε : ℚ.ℚ) (ψ : 0 ℚ.< ε) →
        Close ε ψ (limit approximateBelow approximateBelowCauchy) x
    φ ε ψ = limitClose'
              x approximateBelow
              approximateBelowCauchy
              ε (ε / 3 [ ℚ.3≠0 ]) ψ ψ'
              ψ'' σ'
      where
      ψ' : 0 ℚ.< ε / 3 [ ℚ.3≠0 ]
      ψ' = ℚ.0</' {ε} {3} ψ ℚ.0<3

      ω : ∣ (x - rational (ε / 3 [ ℚ.3≠0 ])) - x ∣ ≡
          rational (ε / 3 [ ℚ.3≠0 ])
      ω = ∣ (x - rational (ε / 3 [ ℚ.3≠0 ])) - x ∣
            ≡⟨ cong ∣_∣
                    (addSubtractLeftCancel x (- rational (ε / 3 [ ℚ.3≠0 ]))) ⟩
          ∣ - rational (ε / 3 [ ℚ.3≠0 ]) ∣
            ≡⟨ magnitudeNegate≡magnitude (rational (ε / 3 [ ℚ.3≠0 ])) ⟩
          ∣ rational (ε / 3 [ ℚ.3≠0 ]) ∣
            ≡⟨ magnitudeRational (ε / 3 [ ℚ.3≠0 ]) ⟩
          rational ℚ.∣ ε / 3 [ ℚ.3≠0 ] ∣
            ≡⟨ 0≤→∣∣≡self (rational (ε / 3 [ ℚ.3≠0 ]))
                          (<→≤ {0} {_} (rationalStrictMonotone {0} ψ')) ⟩
          rational (ε / 3 [ ℚ.3≠0 ]) ∎

      χ : ε / 3 [ ℚ.3≠0 ] ≡ 1 / 3 [ ℚ.3≠0 ] ℚ.· ε
      χ = ε / 3 [ ℚ.3≠0 ]
            ≡⟨ ℚ.·Comm ε (3 [ ℚ.3≠0 ]⁻¹) ⟩
          (3 [ ℚ.3≠0 ]⁻¹) ℚ.· ε
            ≡⟨ cong (flip ℚ._·_ ε) (sym (ℚ.·IdL (3 [ ℚ.3≠0 ]⁻¹))) ⟩
          (1 ℚ.· (3 [ ℚ.3≠0 ]⁻¹)) ℚ.· ε
            ≡⟨ refl ⟩
          1 / 3 [ ℚ.3≠0 ] ℚ.· ε ∎

      π : ε ℚ.- (ε / 3 [ ℚ.3≠0 ]) ≡ 2 / 3 [ ℚ.3≠0 ] ℚ.· ε
      π = ε ℚ.- (ε / 3 [ ℚ.3≠0 ])
            ≡⟨ cong (ℚ._-_ ε) χ ⟩
          ε ℚ.- ((1 / 3 [ ℚ.3≠0 ]) ℚ.· ε)
            ≡⟨ cong (ℚ._+_ ε) (ℚ.-·≡-· (1 / 3 [ ℚ.3≠0 ]) ε) ⟩
          ε ℚ.+ ((ℚ.- (1 / 3 [ ℚ.3≠0 ])) ℚ.· ε)
            ≡⟨ cong (λ ?x → ?x ℚ.+ ((ℚ.- (1 / 3 [ ℚ.3≠0 ])) ℚ.· ε))
                    (sym (ℚ.·IdL ε)) ⟩
          1 ℚ.· ε ℚ.+ ((ℚ.- (1 / 3 [ ℚ.3≠0 ])) ℚ.· ε)
            ≡⟨ sym (ℚ.·DistR+ 1 (ℚ.- (1 / 3 [ ℚ.3≠0 ])) ε) ⟩
          (1 ℚ.- (1 / 3 [ ℚ.3≠0 ])) ℚ.· ε
            ≡⟨ refl ⟩
          2 / 3 [ ℚ.3≠0 ] ℚ.· ε ∎

      ρ : 1 / 3 [ ℚ.3≠0 ] ℚ.< 2 / 3 [ ℚ.3≠0 ]
      ρ = Bool.toWitness {Q = ℚ.<Dec (1 / 3 [ ℚ.3≠0 ]) (2 / 3 [ ℚ.3≠0 ])} tt

      ρ' : ε / 3 [ ℚ.3≠0 ] ℚ.< ε ℚ.- (ε / 3 [ ℚ.3≠0 ])
      ρ' = subst2 ℚ._<_
                  (sym χ) (sym π)
                  (ℚ.<-·o (1 / 3 [ ℚ.3≠0 ]) (2 / 3 [ ℚ.3≠0 ]) ε ψ ρ)

      σ : ∣ (x - rational (ε / 3 [ ℚ.3≠0 ])) - x ∣ <
          rational (ε ℚ.- (ε / 3 [ ℚ.3≠0 ]))
      σ = subst (flip _<_ $ rational (ε ℚ.- (ε / 3 [ ℚ.3≠0 ])))
                (sym ω)
                (rationalStrictMonotone
                  {ε / 3 [ ℚ.3≠0 ]} {ε ℚ.- (ε / 3 [ ℚ.3≠0 ])} ρ')

      ψ'' : 0 ℚ.< ε ℚ.- (ε / 3 [ ℚ.3≠0 ])
      ψ'' = subst (ℚ._<_ 0)
                  (sym π)
                  (ℚ.0<· {2 / 3 [ ℚ.3≠0 ]} {ε}
                         (Bool.toWitness {Q = ℚ.<Dec 0 (2 / 3 [ ℚ.3≠0 ])} tt) ψ)

      σ' : Close (ε ℚ.- (ε / 3 [ ℚ.3≠0 ])) ψ''
                 (x - rational (ε / 3 [ ℚ.3≠0 ])) x
      σ' = distance<→close ψ'' σ

-ε< : (x : ℝ) (ε : ℚ.ℚ) → 0 ℚ.< ε → x - rational ε < x
-ε< x ε φ = ψ'
  where
  φ' : - rational ε < 0
  φ' = -antitone< {0} {rational ε} (rationalStrictMonotone {0} {ε} φ)

  ψ : x - rational ε < x + 0
  ψ = addLeftStrictMonotone { - rational ε } {0} {x} φ'

  ψ' : x - rational ε < x
  ψ' = subst (_<_ $ x - rational ε) (+-unitʳ x) ψ

≤→¬< : {x y : ℝ} → x ≤ y → ¬ y < x
≤→¬< {x} {y} φ ψ = <-irreflexive x ω 
  where
  ω : x < x
  ω = ≤→<→< {x} {y} {x} φ ψ

-- lipschitzMapApproximationApproximateBelow :
--   (x : ℝ) →
--   lipschitzMapApproximation (approximateBelow x)

¬<→≤ : {x y : ℝ} → ¬ x < y → y ≤ x
¬<→≤ {x} {y} φ =
  {!!}
  where
  open ApproximateBelow 0
  open LipschitzMapApproximation
    (flip max (x - y))
    1 ℚ.0<1
    (maxLipschitz₁ (x - y))
    approximateBelow
    approximateBelowCauchy

  foo : limit lipschitzMapApproximation lipschitzMapApproximationCauchy ≡
        max (limit approximateBelow approximateBelowCauchy) (x - y)
  foo = lipschitzMapApproximationLimit

  bar : limit approximateBelow approximateBelowCauchy ≡ 0
  bar = approximateBelowLimit

  buzz : (ε : ℚ.ℚ) (ψ : 0 ℚ.< ε) →
         - rational ε < x - y
  buzz ε ψ = {!!}

  baz : (ε : ℚ.ℚ) (ψ : 0 ℚ.< ε) →
        lipschitzMapApproximation ε ψ ≡
        -- max (0 - rational (ε / 1 [ ≠-symmetric $ ℚ.<→≠ ℚ.0<1 ])) (x - y)
        (flip max (x - y)) (approximateBelow (ε / 1 [ _ ]) _)
  baz ε ψ = refl
    -- max (0 - rational (ε / 1 [ ? ])) (x - y)
    --   ≡⟨ ? ⟩
    -- max (- rational (ε / 1 [ ? ])) (x - y)
    --   ≡⟨ ? ⟩
    -- x - y ∎

  -- f : ℝ → ℝ
  -- f = flip max (x - y)

  -- ψ : Lipschitzℝ f 1 ℚ.0<1
  -- ψ = maxLipschitz₁ (x - y)

  -- z : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ
  -- z = approximateBelow
                       
  -- ω : CauchyApproximation z
  -- ω = approximateBelowCauchy
                             
  -- w : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ
  -- w = lipschitzMapApproximation f 1 ℚ.0<1 z
                                                           
  -- χ : Lipschitzℝ f 1 ℚ.0<1 →
  --      (x₁ : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) →
  --      CauchyApproximation x₁ →
  --      CauchyApproximation (lipschitzMapApproximation f 1 ℚ.0<1 x₁)
  -- χ : CauchyApproximation (lipschitzMapApproximation f 1 ℚ.0<1 z)
  -- χ = lipschitzMapApproximationCauchy f 1 ℚ.0<1 ψ z ω -- ? w ω -- lipschitzMapApproximationCauchy f 1 ℚ.0<1 ψ z ω

  -- foo : limit w χ ≡ max (limit z ω) (x - y)
  -- foo = lipschitzMapApproximationLimit f 1 ℚ.0<1 ψ z ω
        -- (flip max (x - y))
        --   1 ℚ.0<1
        --   ψ
        --   (approximateBelow 0)
        --   (approximateBelowCauchy 0)

  -- bar : limit approximateBelow ω ≡ 0
  -- bar = approximateBelowLimit

-- ≤↔¬< : (x y : ℝ) → (x ≤ y) ↔ (¬ y < x)
-- ≤↔¬< x y = ≤→¬< {x} {y} , ¬<→≤ {y} {x}
