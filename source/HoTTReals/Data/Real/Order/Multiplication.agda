module HoTTReals.Data.Real.Order.Multiplication where

import HoTTReals.Data.Rationals as ℚ
import HoTTReals.Data.Rationals.Order.Base as ℚ
open import Cubical.Algebra.Ring.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary

open BinaryRelation

open import HoTTReals.Data.Real.Base

open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.Reciprocal

open import HoTTReals.Data.Real.Order.Addition.Addition2
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Data.Real.Order.Properties.Properties1
open import HoTTReals.Data.Real.Order.Properties.Properties2

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

open RingTheory ℝRing

multiplyPositve : {x y : ℝ} → 0 < x → 0 < y → 0 < x · y
multiplyPositve {x} {y} φ ψ = χ
  where
  φ' : ∃ ℚ.ℚ (λ ε → (0 < rational ε) × (rational ε < x))
  φ' = <-archimedian 0 x φ

  ψ' : ∃ ℚ.ℚ (λ δ → (0 < rational δ) × (rational δ < y)) 
  ψ' = <-archimedian 0 y ψ

  ω : Σ ℚ.ℚ (λ ε → (0 < rational ε) × (rational ε < x)) →
      Σ ℚ.ℚ (λ δ → (0 < rational δ) × (rational δ < y)) →
      0 < x · y
  ω (ε , χ₁ , π₁) (δ , χ₂ , π₂) = ρ
    where
    χ₁' : 0 ℚ.< ε
    χ₁' = rationalStrictReflective {0} {ε} χ₁

    χ₂' : 0 ℚ.< δ
    χ₂' = rationalStrictReflective {0} {δ} χ₂

    χ : 0 ℚ.< ε ℚ.· δ
    χ = ℚ.0<· {ε} {δ} χ₁' χ₂'

    χ' : 0 < rational (ε ℚ.· δ)
    χ' = rationalStrictMonotone {0} {ε ℚ.· δ} χ

    π : rational (ε ℚ.· δ) ≤ x · y
    π = ·≤· {rational ε} {rational δ} {x} {y}
            (<→≤ {rational ε} {x} π₁) (<→≤ {rational δ} {y} π₂)
            (<→≤ {0} {x} φ) (<→≤ {0} {rational δ} χ₂)

    ρ : 0 < x · y
    ρ = <→≤→< {0} {rational (ε ℚ.· δ)} {x · y} χ' π

  χ : ∃ (ℚ.ℚ × ℚ.ℚ)
        (λ (q , r) → (0 ≤ rational q) × (q ℚ.< r) × (rational r ≤ x · y))
  χ = PropositionalTruncation.rec2 (<-isProp 0 (x · y)) ω φ' ψ'

multiplyPositiveLeftStrictMonotone :
  {x y a : ℝ} → 0 < a → x < y → a · x < a · y
multiplyPositiveLeftStrictMonotone {x} {y} {a} φ ψ = χ
  where
  φ' : ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y))
  φ' = <→∃+ε≤ {x} {y} ψ

  ω : Σ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y)) →
      a · x < a · y
  ω (ε , χ , π) = υ
    where
    ρ : 0 < a · (rational ε)
    ρ = multiplyPositve {a} {rational ε} φ (rationalStrictMonotone {0} {ε} χ)

    σ : a · x + 0 < a · x + a · rational ε
    σ = addLeftStrictMonotone {0} {a · (rational ε)} {a · x} ρ

    σ' : a · x < a · x + a · rational ε
    σ' = subst (flip _<_ $ a · x + a · rational ε) (+-unitʳ $ a · x) σ

    τ : a · (x + rational ε) ≤ a · y
    τ = multiplyNonnegativeLeftMonotone a (x + rational ε) y
                                        (<→≤ {0} {a} φ) π

    τ' : a · x + a · rational ε ≤ a · y
    τ' = subst (flip _≤_ $ a · y) (·-distributesOver-+ˡ a x (rational ε)) τ 

    υ : a · x < a · y
    υ = <→≤→< {a · x} {a · x + a · rational ε} {a · y} σ' τ'

  χ : a · x < a · y
  χ = PropositionalTruncation.rec (<-isProp (a · x) (a · y)) ω φ'

multiplyPositiveRightStrictMonotone : 
  {x y a : ℝ} → 0 < a → x < y → x · a < y · a
multiplyPositiveRightStrictMonotone {x} {y} {a} φ ψ = ω'
  where
  ω : a · x < a · y
  ω = multiplyPositiveLeftStrictMonotone {x} {y} {a} φ ψ

  ω' : x · a < y · a
  ω' = subst2 _<_ (·-commutative a x) (·-commutative a y) ω

leftNonnegative→multiplyPositive→rightPositive :
  {x y : ℝ} → 0 ≤ x → 0 < x · y → 0 < y
leftNonnegative→multiplyPositive→rightPositive {x} {y} φ ψ = ρ
  where
  ω : ∃ ℚ.ℚ (λ ε → (0 < rational ε) × (rational ε < x · y))
  ω = <-archimedian 0 (x · y) ψ

  χ : ∃ ℚ.ℚ (λ δ → (0 ℚ.< δ) × ((∣ x ∣) ≤ rational δ))
  χ = ∣∣≤rational x

  π : Σ ℚ.ℚ (λ ε → (0 < rational ε) × (rational ε < x · y)) →
      Σ ℚ.ℚ (λ δ → (0 ℚ.< δ) × ((∣ x ∣) ≤ rational δ)) →
      0 < y
  π (ε , ρ , σ) (δ , τ , υ) = γ
    where
    ρ' : 0 ℚ.< ε
    ρ' = rationalStrictReflective {0} {ε} ρ

    τ' : ¬ δ ≡ 0
    τ' = ≠-symmetric $ ℚ.<→≠ τ

    τ'' : 0 < rational δ
    τ'' = rationalStrictMonotone {0} {δ} τ

    α : 0 ℚ.< ε ℚ./ δ [ τ' ]
    α = ℚ.0</' {ε} {δ} ρ' τ

    α' : 0 < rational (ε ℚ./ δ [ τ' ])
    α' = rationalStrictMonotone {0} {ε ℚ./ δ [ τ' ]} α

    β : ¬ y < rational (ε ℚ./ δ [ τ' ])
    β γ = ξ
      where
      ζ : ¬ y < 0
      ζ θ = κ
        where
        ι : x · y ≤ x · 0
        -- Agda, why
        ι = let ι' = multiplyNonnegativeLeftMonotone x y 0 φ (<→≤ {y} {0} θ)
            in ι'

        ι' : x · y ≤ 0
        ι' = subst (_≤_ $ x · y) (·-annihilateʳ x) ι

        κ : ⊥
        κ = ≤→¬< ι' ψ

      ζ' : 0 ≤ y
      ζ' = ¬<→≤ ζ

      ι : x · y ≤ ∣ x ∣ · y
      ι = multiplyNonnegativeRightMonotone y x ∣ x ∣ ζ' (self≤∣∣ x)

      κ : ∣ x ∣ · y ≤ rational δ · y
      κ = multiplyNonnegativeRightMonotone y ∣ x ∣ (rational δ) ζ' υ

      μ : rational δ · y < rational ε
      μ = μ''
        where
        μ' : rational δ · y < rational δ · rational (ε ℚ./ δ [ τ' ])
        μ' = multiplyPositiveLeftStrictMonotone
               {y} {rational (ε ℚ./ δ [ τ' ])} {rational δ}
               τ'' γ

        ν : rational δ · rational (ε ℚ./ δ [ τ' ]) ≡ rational ε
        ν = rational δ · rational (ε ℚ./ δ [ τ' ])
              ≡⟨ multiplyRational δ (ε ℚ./ δ [ τ' ]) ⟩
            rational (δ ℚ.· (ε ℚ./ δ [ τ' ]))
              ≡⟨ cong rational (ℚ.·/ ε δ τ') ⟩
            rational ε ∎

        μ'' : rational δ · y < rational ε
        μ'' = subst (_<_ $ rational δ · y) ν μ'


      ν : x · y < x · y
      ν = ≤→<→< {x · y} {∣ x ∣ · y} {x · y}
            ι (≤→<→< {∣ x ∣ · y} {rational δ · y} {x · y}
                     κ (<-transitive (rational δ · y) (rational ε) (x · y) μ σ))

      ξ : ⊥
      ξ = <-irreflexive (x · y) ν

    β' : rational (ε ℚ./ δ [ τ' ]) ≤ y 
    β' = ¬<→≤ β

    γ : 0 < y
    γ = <→≤→< {0} {rational (ε ℚ./ δ [ τ' ])} {y} α' β'

  ρ : 0 < y
  ρ = PropositionalTruncation.rec2 (<-isProp 0 y) π ω χ

positive→reciprocalPositive :
  {x : ℝ} (φ : 0 < x) → 0 < (x [ inr φ ]⁻¹)
positive→reciprocalPositive {x} φ = χ
  where
  ψ : x · reciprocalPositive x φ ≡ 1
  ψ = reciprocalPositiveInverseᵣ x φ

  ω : 0 < x · reciprocalPositive x φ
  ω = <→≤→< {0} {1} {x · reciprocalPositive x φ} 0<1 (≡→≤ $ sym ψ)

  χ : 0 < x [ inr φ ]⁻¹
  χ = leftNonnegative→multiplyPositive→rightPositive
        {x} {reciprocalPositive x φ} (<→≤ {0} {x} φ) ω

multiplyPositiveLeftStrictReflective :
  {x y a : ℝ} → 0 < a → a · x < a · y → x < y
multiplyPositiveLeftStrictReflective {x} {y} {a} φ ψ = χ'
  where
  ω : 0 < a [ inr φ ]⁻¹
  ω = positive→reciprocalPositive φ

  χ : a [ inr φ ]⁻¹ · (a · x) < a [ inr φ ]⁻¹ · (a · y)
  χ = multiplyPositiveLeftStrictMonotone {a · x} {a · y} {a [ inr φ ]⁻¹} ω ψ

  χ' : x < y
  χ' = subst2 _<_ π₁ π₂ χ
    where
    π₁ : a [ inr φ ]⁻¹ · (a · x) ≡ x
    π₁ = a [ inr φ ]⁻¹ · (a · x)
           ≡⟨ (sym $ ·-associative (a [ inr φ ]⁻¹) a x) ⟩
         (a [ inr φ ]⁻¹ · a) · x
           ≡⟨ cong (flip _·_ x) (⁻¹-inverseₗ a (inr φ)) ⟩
         1 · x
           ≡⟨ ·-unitˡ x ⟩
         x ∎

    π₂ : a [ inr φ ]⁻¹ · (a · y) ≡ y
    π₂ = a [ inr φ ]⁻¹ · (a · y)
           ≡⟨ (sym $ ·-associative (a [ inr φ ]⁻¹) a y) ⟩
         (a [ inr φ ]⁻¹ · a) · y
           ≡⟨ cong (flip _·_ y) (⁻¹-inverseₗ a (inr φ)) ⟩
         1 · y
           ≡⟨ ·-unitˡ y ⟩
         y ∎

multiplyPositiveRightStrictReflective :
  {x y a : ℝ} → 0 < a → x · a < y · a → x < y
multiplyPositiveRightStrictReflective {x} {y} {a} φ ψ = ω
  where
  ψ' : a · x < a · y
  ψ' = subst2 _<_ (·-commutative x a) (·-commutative y a) ψ

  ω : x < y
  ω = multiplyPositiveLeftStrictReflective {x} {y} {a} φ ψ'

invertible→apartZero : 
  {x y : ℝ} → x · y ≡ 1 → x # 0
invertible→apartZero {x} {y} φ = χ
  where
  ψ : ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q))
  ψ = ∣∣≤rational y

  ω : Σ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ y ∣ ≤ rational q)) →
      0 < ∣ x ∣
  ω (q , χ , π) = υ
    where
    ρ : ∣ x ∣ · ∣ y ∣ ≡ 1
    ρ = ∣ x ∣ · ∣ y ∣
          ≡⟨ (sym $ magnitudeMultiply≡multiplyMagnitude x y) ⟩
        ∣ x · y ∣
          ≡⟨ cong ∣_∣ φ ⟩
        ∣ 1 ∣
          ≡⟨ magnitudeRational 1 ⟩
        1 ∎

    σ : ∣ x ∣ · ∣ y ∣ ≤ ∣ x ∣ · rational q
    σ = multiplyNonnegativeLeftMonotone
          (∣ x ∣) (∣ y ∣) (rational q)
          (0≤magnitude x) π

    σ' : 1 ≤ ∣ x ∣ · rational q
    σ' = ≤-transitive 1 (∣ x ∣ · ∣ y ∣) (∣ x ∣ · rational q)
                      (≡→≤ $ sym ρ) σ 

    χ' : ¬ q ≡ 0
    χ' = ≠-symmetric $ ℚ.<→≠ χ

    χ'' : 0 ℚ.< q ℚ.[ χ' ]⁻¹
    χ'' = ℚ.0<⁻¹' {q} χ

    τ : 1 · rational (q ℚ.[ χ' ]⁻¹) ≤
        (∣ x ∣ · rational q) · rational (q ℚ.[ χ' ]⁻¹)
    τ = multiplyNonnegativeRightMonotone
          (rational (q ℚ.[ χ' ]⁻¹)) 1 (∣ x ∣ · rational q)
          (<→≤ {0} {rational (q ℚ.[ χ' ]⁻¹)} $
           rationalStrictMonotone {0} {q ℚ.[ χ' ]⁻¹} χ'') σ'

    τ' : rational (q ℚ.[ χ' ]⁻¹) ≤ ∣ x ∣
    τ' = subst2 _≤_ α γ τ
      where
      α : 1 · rational (q ℚ.[ χ' ]⁻¹) ≡ rational (q ℚ.[ χ' ]⁻¹)
      α = ·-unitˡ $ rational (q ℚ.[ χ' ]⁻¹)

      β : q ℚ.· (q ℚ.[ χ' ]⁻¹) ≡ 1
      β = ℚ.⁻¹-inverse q χ'

      β' : rational (q ℚ.· (q ℚ.[ χ' ]⁻¹)) ≡ 1
      β' = cong rational β

      γ : (∣ x ∣ · rational q) · rational (q ℚ.[ χ' ]⁻¹) ≡ ∣ x ∣
      γ = (∣ x ∣ · rational q) · rational (q ℚ.[ χ' ]⁻¹)
             ≡⟨ ·-associative ∣ x ∣ (rational q) (rational (q ℚ.[ χ' ]⁻¹)) ⟩
          ∣ x ∣ · (rational q · rational (q ℚ.[ χ' ]⁻¹))
             ≡⟨ cong (_·_ ∣ x ∣) (multiplyRational q  (q ℚ.[ χ' ]⁻¹)) ⟩
          ∣ x ∣ · rational (q ℚ.· (q ℚ.[ χ' ]⁻¹))
            ≡⟨ cong (_·_ ∣ x ∣) β' ∙ ·-unitʳ ∣ x ∣ ⟩
          ∣ x ∣ ∎

    υ : 0 < ∣ x ∣
    υ = <→≤→< {0} {rational (q ℚ.[ χ' ]⁻¹)} {∣ x ∣}
              (rationalStrictMonotone {0} {q ℚ.[ χ' ]⁻¹} χ'') τ'

  χ : x # 0
  χ = PropositionalTruncation.rec
        (#-isProp x 0)
        (magnitudePositive→apartZero ∘ ω)
        ψ

invertible↔apartZero :
  (x : ℝ) →
  Σ ℝ (λ y → x · y ≡ 1) ↔ (x # 0)
invertible↔apartZero x =
  (λ (y , φ) → invertible→apartZero {x} {y} φ) ,
  (λ φ → (x [ φ ]⁻¹) , ⁻¹-inverseᵣ x φ)
