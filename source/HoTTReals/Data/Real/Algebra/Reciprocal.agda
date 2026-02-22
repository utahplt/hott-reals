module HoTTReals.Data.Real.Algebra.Reciprocal where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Nat.Literals public
open import Cubical.Algebra.Ring.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
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
open import HoTTReals.Data.Real.Algebra.Multiplication

open import HoTTReals.Data.Real.Order.Addition.Addition1
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Distance
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Data.Real.Order.Properties.Properties1
open import HoTTReals.Data.Real.Order.Properties.Properties2

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

open RingTheory ℝRing

-- TODO: This is a hack to get Agda to type check
-- `boundedReciprocalPositiveLipschitz` without stalling. With my previous code,
-- Agda had to use normalization to check whether the arguments to
-- liftLipschitzLipschitz were definitionally equal and it hung forever trying
-- to do this
module BoundedReciprocalPositive (δ : ℚ.ℚ) (φ : 0 ℚ.< δ) where
  private
    ψ : ¬ δ ≡ 0
    ψ = ≠-symmetric $ ℚ.<→≠ φ

    φ' : 0 ℚ.< δ ℚ.· δ
    φ' = ℚ.0<· {x = δ} {y = δ} φ φ

    ψ' : ¬ δ ℚ.· δ ≡ 0
    ψ' = ≠-symmetric $ ℚ.<→≠ φ'

    L : ℚ.ℚ
    L = (δ ℚ.· δ) ℚ.[ ψ' ]⁻¹

    φ'' : 0 ℚ.< L
    φ'' = ℚ.0<⁻¹' {x = δ ℚ.· δ} φ'

  boundedReciprocalPositiveRational : ℚ.ℚ → ℚ.ℚ
  boundedReciprocalPositiveRational q = (ℚ.max q δ) ℚ.[ ω' ]⁻¹
    where
    ω : 0 ℚ.< ℚ.max q δ
    ω = ℚ.isTrans<≤ 0 δ (ℚ.max q δ) φ (ℚ.≤max' q δ)
                                                     
    ω' : ¬ ℚ.max q δ ≡ 0
    ω' = ≠-symmetric $ ℚ.<→≠ ω

  reciprocalMaxLipschitzℚ : 
    Lipschitzℚ
      (rational ∘ boundedReciprocalPositiveRational)
      ((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹)
      φ''
  reciprocalMaxLipschitzℚ q r ε χ π = γ''
    where
    ω : 0 ℚ.< ℚ.max q δ
    ω = ℚ.isTrans<≤ 0 δ (ℚ.max q δ) φ (ℚ.≤max' q δ)
  
    ω' : ¬ ℚ.max q δ ≡ 0
    ω' = ≠-symmetric $ ℚ.<→≠ ω
  
    σ : 0 ℚ.< ℚ.max r δ
    σ = ℚ.isTrans<≤ 0 δ (ℚ.max r δ) φ (ℚ.≤max' r δ)
  
    σ' : ¬ ℚ.max r δ ≡ 0
    σ' = ≠-symmetric $ ℚ.<→≠ σ
  
    τ : 0 ℚ.< ℚ.max q δ ℚ.· ℚ.max r δ
    τ = ℚ.0<· {x = ℚ.max q δ} {y = ℚ.max r δ} ω σ
  
    τ' : ¬ ℚ.max q δ ℚ.· ℚ.max r δ ≡ 0
    τ' = ≠-symmetric $ ℚ.<→≠ τ
  
    τ'' : 0 ℚ.< (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹
    τ'' = ℚ.0<⁻¹' {x = ℚ.max q δ ℚ.· ℚ.max r δ} τ
  
    υ : δ ℚ.· δ ℚ.≤ ℚ.max q δ ℚ.· ℚ.max r δ
    υ = ℚ.·≤· {x = δ} {y = δ} {z = ℚ.max q δ} {w = ℚ.max r δ}
              (ℚ.≤max' q δ) (ℚ.≤max' r δ)
              (ℚ.<Weaken≤ 0 (ℚ.max q δ) ω) (ℚ.<Weaken≤ 0 δ φ)
  
    υ' : ((ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹) ℚ.≤ ((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹)
    υ' = ℚ.⁻¹-positiveAntitone
         {x = δ ℚ.· δ} {y = (ℚ.max q δ) ℚ.· (ℚ.max r δ)}
           φ' υ ψ' τ'
  
    α : Close ε χ (rational (ℚ.max q δ)) (rational (ℚ.max r δ))
    α = fst maxNonexpandingℝ₂
        (rational δ) (rational q) (rational r)
          ε χ
          (close'→close (rational q) (rational r) ε χ π)
  
    α' : distance (rational (ℚ.max q δ)) (rational (ℚ.max r δ)) < rational ε
    α' = close→distance< χ α
  
    α'' : ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣ ℚ.< ε
    α'' = rationalStrictReflective {q = ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣} {r = ε}
                                   α'
  
    β : ℚ.∣ ((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣ ≡
        (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹ ℚ.· ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣
    β = ℚ.∣ ((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ?x ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣)
                   (sym $ ℚ.·IdR $ (ℚ.max q δ) ℚ.[ ω' ]⁻¹) ⟩
        ℚ.∣ (((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· 1) ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣
          ≡⟨ cong (λ ?x → ℚ.∣ (((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ?x) ℚ.-
                              ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣)
                  (sym $ ℚ.⁻¹-inverse' (ℚ.max r δ) σ') ⟩
        ℚ.∣ (((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.·
            (((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ℚ.· (ℚ.max r δ))) ℚ.-
            ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ?x ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣)
                   (ℚ.·Assoc ((ℚ.max q δ) ℚ.[ ω' ]⁻¹)
                             (ℚ.max r δ ℚ.[ σ' ]⁻¹)
                             (ℚ.max r δ)) ⟩
        ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
            (ℚ.max r δ)) ℚ.-
            ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.·
                            ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
                              (ℚ.max r δ)) ℚ.- ?x ∣)
                   (sym $ ℚ.·IdR $ (ℚ.max r δ) ℚ.[ σ' ]⁻¹) ⟩
        ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
            (ℚ.max r δ)) ℚ.-
            (((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ℚ.· 1) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.·
                            ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
                              (ℚ.max r δ)) ℚ.-
                              (((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ℚ.· ?x) ∣)
                   (sym $ ℚ.⁻¹-inverse' (ℚ.max q δ) ω') ⟩
        ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
            (ℚ.max r δ)) ℚ.-
            (((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ℚ.·
              (((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· (ℚ.max q δ))) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.·
                            ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
                              (ℚ.max r δ)) ℚ.-
                              ?x ∣)
                   (ℚ.·Assoc (((ℚ.max r δ) ℚ.[ σ' ]⁻¹))
                             (ℚ.max q δ ℚ.[ ω' ]⁻¹)
                             (ℚ.max q δ)) ⟩
        ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
            (ℚ.max r δ)) ℚ.-
            ((((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ℚ.· ((ℚ.max q δ) ℚ.[ ω' ]⁻¹)) ℚ.·
              (ℚ.max q δ)) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.·
                            ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
                              (ℚ.max r δ)) ℚ.-
                              (?x ℚ.· (ℚ.max q δ)) ∣)
                   (ℚ.·Comm (ℚ.max r δ ℚ.[ σ' ]⁻¹)
                            (ℚ.max q δ ℚ.[ ω' ]⁻¹)) ⟩
        ℚ.∣ ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
            (ℚ.max r δ)) ℚ.-
            ((((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ℚ.·
              (ℚ.max q δ)) ∣
        ≡⟨ ℚ.·distanceₗ (((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹))
                        (ℚ.max r δ)
                          (ℚ.max q δ) ⟩
        ℚ.∣ (((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) ℚ.[ σ' ]⁻¹)) ∣ ℚ.·
        ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣
          ≡⟨ cong (λ ?x → (ℚ.∣ ?x ∣) ℚ.· (ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣))
                  (sym $ ℚ.·⁻¹' (ℚ.max q δ) (ℚ.max r δ) ω' σ' τ') ⟩
        ℚ.∣ (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹ ∣ ℚ.·
        ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣
          ≡⟨ cong
               (flip ℚ._·_ $ ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣)
               (ℚ.0≤→∣∣≡self
                 (((ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹))
                 (ℚ.<Weaken≤ 0 ((ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹) τ'') ) ⟩
        ((ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹) ℚ.·
        ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣
          ≡⟨ cong (ℚ._·_ $ (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹)
                  (ℚ.distanceCommutative (ℚ.max r δ) (ℚ.max q δ)) ⟩
        (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹ ℚ.·
        ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣ ∎
  
    γ : (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹ ℚ.·
         ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣ ℚ.<
        ((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹) ℚ.· ε
    γ = ℚ.≤→<→·<·
        {x = (ℚ.max q δ ℚ.· ℚ.max r δ) ℚ.[ τ' ]⁻¹}
          {y = ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣}
          {z = (δ ℚ.· δ) ℚ.[ ψ' ]⁻¹}
          {w = ε}
          υ' α''
          φ''
          (ℚ.0≤∣∣ $ ℚ.max q δ ℚ.- ℚ.max r δ)
  
    γ' : ℚ.∣ ((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣ ℚ.<
         ((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹) ℚ.· ε
    γ' = subst (flip ℚ._<_ $ ((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹) ℚ.· ε)
               (sym β)
               γ
  
    γ'' : Close
          (((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹) ℚ.· ε)
            (ℚ.0<· {x = (δ ℚ.· δ) ℚ.[ ψ' ]⁻¹} {y = ε} φ'' χ)
            (rational ((ℚ.max q δ) ℚ.[ ω' ]⁻¹))
            (rational ((ℚ.max r δ) ℚ.[ σ' ]⁻¹))
    γ'' = distance<→close
          _
            (rationalStrictMonotone
              {q = ℚ.∣ ((ℚ.max q δ) ℚ.[ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) ℚ.[ σ' ]⁻¹) ∣}
              {r = ((δ ℚ.· δ) ℚ.[ ψ' ]⁻¹) ℚ.· ε}
              γ')

  boundedReciprocalPositive : ℝ → ℝ
  boundedReciprocalPositive =
    liftLipschitz (rational ∘ boundedReciprocalPositiveRational)
                  L φ''
                  reciprocalMaxLipschitzℚ

  boundedReciprocalPositveRational≡boundedReciprocalPositiveRational :
    (boundedReciprocalPositive ∘ rational) ∼
    (rational ∘ boundedReciprocalPositiveRational)
  boundedReciprocalPositveRational≡boundedReciprocalPositiveRational q = refl

  boundedReciprocalPositiveLipschitz :
    Lipschitzℝ boundedReciprocalPositive L φ''
  boundedReciprocalPositiveLipschitz =
    liftLipschitzLipschitz (rational ∘ boundedReciprocalPositiveRational)
                           L φ''
                           reciprocalMaxLipschitzℚ

  boundedReciprocalPositiveContinuous :
    Continuous boundedReciprocalPositive
  boundedReciprocalPositiveContinuous =
    lipschitz→continuous boundedReciprocalPositive
                         L φ''
                         boundedReciprocalPositiveLipschitz

open BoundedReciprocalPositive public

boundedReciprocalPositive≤→≡ :
  (δ₁ δ₂ : ℚ.ℚ) (φ₁ : 0 ℚ.< δ₁) (φ₂ : 0 ℚ.< δ₂) →
  δ₁ ℚ.≤ δ₂ →
  (x : ℝ) →
  boundedReciprocalPositive δ₁ φ₁ (max x (rational δ₂)) ≡
  boundedReciprocalPositive δ₂ φ₂ x
boundedReciprocalPositive≤→≡ δ₁ δ₂ φ₁ φ₂ ψ =
  continuousExtensionLaw₁
    f g f' g'
    ω χ π ρ σ
  where
  f : ℝ → ℝ
  f x = boundedReciprocalPositive δ₁ φ₁ (max x (rational δ₂))

  g : ℝ → ℝ
  g = boundedReciprocalPositive δ₂ φ₂

  f' : ℚ.ℚ → ℚ.ℚ
  f' = boundedReciprocalPositiveRational δ₁ φ₁ ∘ (flip ℚ.max δ₂)

  g' : ℚ.ℚ → ℚ.ℚ
  g' = boundedReciprocalPositiveRational δ₂ φ₂

  ω : (f ∘ rational) ∼ (rational ∘ f')
  ω q = refl

  χ : (g ∘ rational) ∼ (rational ∘ g')
  χ q = refl

  π : f' ∼ g'
  π q = τ
    where
    ω'₁ : ¬ ℚ.max (ℚ.max q δ₂) δ₁ ≡ 0
    ω'₁ = ≠-symmetric $ ℚ.<→≠ $
      ℚ.isTrans<≤ 0 δ₁ (ℚ.max (ℚ.max q δ₂) δ₁) φ₁ (ℚ.≤max' (ℚ.max q δ₂) δ₁)

    ω'₂ : ¬ ℚ.max q δ₂ ≡ 0
    ω'₂ = ≠-symmetric $ ℚ.<→≠ $
      ℚ.isTrans<≤ 0 δ₂ (ℚ.max q δ₂) φ₂ (ℚ.≤max' q δ₂)

    σ : ℚ.max (ℚ.max q δ₂) δ₁ ≡ ℚ.max q δ₂
    σ = ℚ.≤→max' {x = ℚ.max q δ₂} {y = δ₁}
          (ℚ.isTrans≤ δ₁ δ₂ (ℚ.max q δ₂) ψ (ℚ.≤max' q δ₂))

    τ : f' q ≡ g' q
    τ = λ i → σ i ℚ.[ isProp→PathP (λ i → isProp¬ (σ i ≡ 0)) ω'₁ ω'₂ i ]⁻¹

  ρ : Continuous f
  ρ = continuousCompose
        (flip max (rational δ₂))
        (boundedReciprocalPositive δ₁ φ₁)
        (maxContinuous₁ (rational δ₂))
        (boundedReciprocalPositiveContinuous δ₁ φ₁)

  σ : Continuous g
  σ = boundedReciprocalPositiveContinuous δ₂ φ₂

boundedReciprocalPositiveCurried :
  (x : ℝ) →
  Σ ℚ.ℚ (λ δ → (0 ℚ.< δ) × (rational δ ≤ x)) → ℝ
boundedReciprocalPositiveCurried x (δ , φ , ψ) =
  boundedReciprocalPositive δ φ x

boundedReciprocalPositiveCurriedIs2Constant :
  (x : ℝ) →
  2-Constant (boundedReciprocalPositiveCurried x)
boundedReciprocalPositiveCurriedIs2Constant x (δ₁ , φ₁ , ψ₁) (δ₂ , φ₂ , ψ₂) = τ
  where
  δ : ℚ.ℚ
  δ = ℚ.min δ₁ δ₂

  ω₁ : δ ℚ.≤ δ₁
  ω₁ = ℚ.min≤ δ₁ δ₂

  ω₂ : δ ℚ.≤ δ₂
  ω₂ = ℚ.min≤' δ₁ δ₂

  χ : 0 ℚ.< δ
  χ = ℚ.minGreatestLowerBound< {x = δ₁} {y = δ₂} {z = 0} φ₁ φ₂

  π : rational δ ≤ x
  π = ≤-transitive (rational δ) (rational δ₁) x
                   (rationalMonotone {q = δ} {r = δ₁} ω₁) ψ₁

  ρ₁ : boundedReciprocalPositive δ χ (max x (rational δ₁)) ≡
       boundedReciprocalPositive δ₁ φ₁ x
  ρ₁ = boundedReciprocalPositive≤→≡ δ δ₁ χ φ₁ ω₁ x

  ρ₂ : boundedReciprocalPositive δ χ (max x (rational δ₂)) ≡
       boundedReciprocalPositive δ₂ φ₂ x
  ρ₂ = boundedReciprocalPositive≤→≡ δ δ₂ χ φ₂ ω₂ x

  σ₁ : max x (rational δ₁) ≡ x
  σ₁ = max x (rational δ₁)
         ≡⟨ maxCommutative x (rational δ₁) ⟩
       max (rational δ₁) x
         ≡⟨ ψ₁ ⟩
       x ∎

  ρ₁' : boundedReciprocalPositive δ χ x ≡
        boundedReciprocalPositive δ₁ φ₁ x
  ρ₁' = boundedReciprocalPositive δ χ x
          ≡⟨ cong (boundedReciprocalPositive δ χ) (sym σ₁) ⟩
        boundedReciprocalPositive δ χ (max x (rational δ₁))
          ≡⟨ ρ₁ ⟩
        boundedReciprocalPositive δ₁ φ₁ x ∎

  σ₂ : max x (rational δ₂) ≡ x
  σ₂ = max x (rational δ₂)
         ≡⟨ maxCommutative x (rational δ₂) ⟩
       max (rational δ₂) x
         ≡⟨ ψ₂ ⟩
       x ∎

  ρ₂' : boundedReciprocalPositive δ χ x ≡
        boundedReciprocalPositive δ₂ φ₂ x
  ρ₂' = boundedReciprocalPositive δ χ x
          ≡⟨ cong (boundedReciprocalPositive δ χ) (sym σ₂) ⟩
        boundedReciprocalPositive δ χ (max x (rational δ₂))
          ≡⟨ ρ₂ ⟩
        boundedReciprocalPositive δ₂ φ₂ x ∎

  τ : boundedReciprocalPositive δ₁ φ₁ x ≡
      boundedReciprocalPositive δ₂ φ₂ x
  τ = sym ρ₁' ∙ ρ₂'

0<→existsPositiveRational≤ :
  {x : ℝ} → 0 < x → ∃ ℚ.ℚ (λ δ → (0 ℚ.< δ) × (rational δ ≤ x))
0<→existsPositiveRational≤ {x} φ =
  PropositionalTruncation.map ψ ω
  where
  ψ : Σ ℚ.ℚ (λ δ → (0 < rational δ) × (rational δ < x)) →
      Σ ℚ.ℚ (λ δ → (0 ℚ.< δ) × (rational δ ≤ x))
  ψ (δ , (ω , χ)) = δ , (rationalStrictReflective {q = 0} {r = δ} ω ,
                         <→≤ {x = rational δ} {y = x} χ)

  ω : ∃ ℚ.ℚ (λ q → (0 < rational q) × (rational q < x))
  ω = <-archimedian 0 x φ

reciprocalPositive : (x : ℝ) → 0 < x → ℝ
reciprocalPositive x φ =
  SetElim.rec→Set
    ℝ-isSet
    (boundedReciprocalPositiveCurried x)
    (boundedReciprocalPositiveCurriedIs2Constant x)
    (0<→existsPositiveRational≤ φ)

_[_]⁻¹ : (x : ℝ) → x # 0 → ℝ
x [ inl φ ]⁻¹ = - reciprocalPositive (- x) (-antitone< {x = x} {y = 0} φ)
x [ inr φ ]⁻¹ = reciprocalPositive x φ

reciprocalPositive≡boundedReciprocalPositive :
  (δ : ℚ.ℚ) (φ : 0 ℚ.< δ)
  (x : ℝ) (ψ : rational δ ≤ x) (ω : 0 < x) →
  reciprocalPositive x ω ≡ boundedReciprocalPositive δ φ x
reciprocalPositive≡boundedReciprocalPositive δ φ x ψ ω =
  SetElim.helper
    ℝ-isSet
    (boundedReciprocalPositiveCurried x)
    (boundedReciprocalPositiveCurriedIs2Constant x)
    χ
    π
  where
  χ : ∃ ℚ.ℚ (λ δ → (0 ℚ.< δ) × (rational δ ≤ x))
  χ = 0<→existsPositiveRational≤ ω

  π : ∃ ℚ.ℚ (λ δ → (0 ℚ.< δ) × (rational δ ≤ x))
  π = ∣ δ , (φ , ψ) ∣₁

-- Bespoke continuity argument for the needed expression because I'm lazy right
-- now and don't want to do it the proper way
maxMultiplyBoundedReciprocalPositiveContinuous :
  (δ : ℚ.ℚ) (φ : 0 ℚ.< δ) →
  Continuous $ (λ x → max x (rational δ) · boundedReciprocalPositive δ φ x)
maxMultiplyBoundedReciprocalPositiveContinuous δ φ x ε ψ = ρ
  where
  ψ' : 0 ℚ.< ε ℚ./ 2 [ ℚ.2≠0 ]
  ψ' = ℚ.0</' {ε} {2} ψ ℚ.0<2

  ω : ∃ ℚ.ℚ
      (λ η₁ →
      Σ (0 ℚ.< η₁)
      (λ ζ →
      (y : ℝ) →
      Close η₁ ζ x y →
      Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
            (max x (rational δ) · boundedReciprocalPositive δ φ x)
            (max y (rational δ) · boundedReciprocalPositive δ φ x)))
  ω = continuousCompose
        (flip max (rational δ)) (flip _·_ $ boundedReciprocalPositive δ φ x)
        (maxContinuous₁ $ rational δ)
        (multiplyContinuous₁ $ boundedReciprocalPositive δ φ x)
        x (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'

  χ : ∃ ℚ.ℚ
      (λ η₂ →
      Σ (0 ℚ.< η₂)
      (λ ζ →
      (y : ℝ) →
      Close η₂ ζ x y →
      Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
            (max y (rational δ) · boundedReciprocalPositive δ φ x)
            (max y (rational δ) · boundedReciprocalPositive δ φ y)))
  χ = PropositionalTruncation.rec isPropPropTrunc χ' π
    where
    π : ∃ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ max x (rational δ) ∣ ≤ rational L))
    π = ∣∣≤rational $ max x (rational δ)

    χ' : Σ ℚ.ℚ (λ L → (0 ℚ.< L) × (∣ max x (rational δ) ∣ ≤ rational L)) →
         ∃ ℚ.ℚ
         (λ η₂ →
         Σ (0 ℚ.< η₂)
         (λ ζ →
         (y : ℝ) →
         Close η₂ ζ x y →
         Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
         (max y (rational δ) · boundedReciprocalPositive δ φ x)
         (max y (rational δ) · boundedReciprocalPositive δ φ y)))
    χ' (L , ρ , σ) = PropositionalTruncation.rec isPropPropTrunc χ'' α 
      where
      τ : 0 ℚ.< L ℚ.+ 1
      τ = ℚ.0<+' {L} {1} ρ ℚ.0<1

      τ' : ¬ (L ℚ.+ 1) ≡ 0
      τ' = ≠-symmetric $ ℚ.<→≠ τ

      ε' : ℚ.ℚ
      ε' = (L ℚ.+ 1) ℚ.[ τ' ]⁻¹ ℚ.· (ε ℚ./ 2 [ ℚ.2≠0 ])
  
      υ : 0 ℚ.< ε'
      υ = ℚ.0<· {x = (L ℚ.+ 1) ℚ.[ τ' ]⁻¹} {y = ε ℚ./ 2 [ ℚ.2≠0 ]}
                (ℚ.0<⁻¹' {x = L ℚ.+ 1} τ) ψ'

      α : ∃ ℚ.ℚ
          (λ θ → Σ (0 ℚ.< θ) (λ ζ →
          (y : ℝ) →
          Close θ ζ x y →
          Close ε' υ (boundedReciprocalPositive δ φ x)
                     (boundedReciprocalPositive δ φ y)))
      α = boundedReciprocalPositiveContinuous δ φ x ε' υ

      χ'' : Σ ℚ.ℚ
            (λ θ →
            Σ (0 ℚ.< θ)
            (λ ζ →
            (y : ℝ) →
            Close θ ζ x y →
            Close ε' υ (boundedReciprocalPositive δ φ x)
                       (boundedReciprocalPositive δ φ y))) →
            ∃ ℚ.ℚ
            (λ η₂ →
            Σ (0 ℚ.< η₂)
            (λ ζ →
            (y : ℝ) →
            Close η₂ ζ x y →
            Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
                  (max y (rational δ) · boundedReciprocalPositive δ φ x)
                  (max y (rational δ) · boundedReciprocalPositive δ φ y)))
      χ'' (θ , β , γ) = ∣ η₂ , (β' , ζ) ∣₁
        where
        η₂ : ℚ.ℚ
        η₂ = ℚ.min θ 1

        β' : 0 ℚ.< ℚ.min θ 1
        β' = ℚ.minGreatestLowerBound< {θ} {1} {0} β ℚ.0<1

        ζ : (y : ℝ) →
            Close η₂ β' x y →
            Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
                  (max y (rational δ) · boundedReciprocalPositive δ φ x)
                  (max y (rational δ) · boundedReciprocalPositive δ φ y)
        ζ y ι = Φ''
          where
          ι' : distance x y < rational η₂
          ι' = close→distance< β' ι

          ι'' : distance x y < rational θ
          ι'' = <→≤→< {distance x y} {rational (ℚ.min θ 1)} {rational θ}
                      ι' (rationalMonotone {ℚ.min θ 1} {θ} $ ℚ.min≤ θ 1)

          ι''' : Close θ β x y
          ι''' = distance<→close β ι''

          κ : Close ε' υ
                    (boundedReciprocalPositive δ φ x)
                    (boundedReciprocalPositive δ φ y)
          κ = γ y ι''' 

          μ : distance x y < 1
          μ = (<→≤→< {distance x y} {rational (ℚ.min θ 1)} {rational 1}
                     ι' (rationalMonotone {ℚ.min θ 1} {1} $ ℚ.min≤' θ 1))

          μ' : Close 1 ℚ.0<1 x y
          μ' = distance<→close ℚ.0<1 μ

          ν : Close 1 ℚ.0<1 (max x (rational δ)) (max y (rational δ))
          ν = fst maxNonexpandingℝ₂ (rational δ) x y 1 ℚ.0<1 μ'

          ξ : max y (rational δ) ≤ max x (rational δ) + 1
          ξ = close→≤+ε ℚ.0<1 ν

          ξ' : max y (rational δ) ≤ rational (L ℚ.+ 1)
          ξ' = ≤-transitive
                 (max y (rational δ))
                 (max x (rational δ) + 1)
                 (rational $ L ℚ.+ 1)
                 ξ
                 (addRightMonotone
                   {max x (rational δ)} {rational L} {1}
                   (≤-transitive (max x (rational δ))
                                 ∣ max x (rational δ) ∣
                                 (rational L)
                                 (self≤∣∣ $ max x (rational δ))
                                 σ))

          ο : 0 ≤ max y (rational δ)
          ο = ≤-transitive 0 (rational δ) (max y (rational δ))
                (<→≤ {0} {rational δ} (rationalStrictMonotone {0} {δ} φ))
                (≤-max₂ y (rational δ))

          ξ'' : ∣ max y (rational δ) ∣ ≤ rational (L ℚ.+ 1)
          ξ'' = subst (flip _≤_ $ rational (L ℚ.+ 1))
                      (sym $ 0≤→∣∣≡self (max y (rational δ)) ο)
                      ξ'

          Φ : Close ((L ℚ.+ 1) ℚ.· ε')
                    (ℚ.0<· {L ℚ.+ 1} {ε'} τ υ)
                    (max y (rational δ) · boundedReciprocalPositive δ φ x)
                    (max y (rational δ) · boundedReciprocalPositive δ φ y)
          Φ = multiplyLipscthiz₂
                (L ℚ.+ 1) τ
                (max y (rational δ)) ξ''
                (boundedReciprocalPositive δ φ x)
                (boundedReciprocalPositive δ φ y)
                ε' υ κ

          Ψ : (L ℚ.+ 1) ℚ.· ε' ≡ ε ℚ./ 2 [ ℚ.2≠0 ]
          Ψ = (L ℚ.+ 1) ℚ.· ((L ℚ.+ 1) ℚ.[ τ' ]⁻¹ ℚ.· (ε ℚ./ 2 [ ℚ.2≠0 ]))
                 ≡⟨ ℚ.·Assoc (L ℚ.+ 1)
                             ((L ℚ.+ 1) ℚ.[ τ' ]⁻¹)
                             (ε ℚ./ 2 [ ℚ.2≠0 ]) ⟩
              ((L ℚ.+ 1) ℚ.· (L ℚ.+ 1) ℚ.[ τ' ]⁻¹) ℚ.· (ε ℚ./ 2 [ ℚ.2≠0 ])
                ≡⟨ cong (flip ℚ._·_ (ε ℚ./ 2 [ ℚ.2≠0 ]))
                        (ℚ.⁻¹-inverse (L ℚ.+ 1) τ') ⟩
              1 ℚ.· (ε ℚ./ 2 [ ℚ.2≠0 ])
                ≡⟨ ℚ.·IdL _ ⟩
              ε ℚ./ 2 [ ℚ.2≠0 ] ∎

          Φ' : Σ (0 ℚ.< ε ℚ./ 2 [ ℚ.2≠0 ])
                 (λ ξ →
                   Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ξ 
                     (max y (rational δ) · boundedReciprocalPositive δ φ x)
                     (max y (rational δ) · boundedReciprocalPositive δ φ y))
          Φ' = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ
                       (max y (rational δ) · boundedReciprocalPositive δ φ x)
                       (max y (rational δ) · boundedReciprocalPositive δ φ y)))
                     Ψ
                     ((_ , Φ))

          Φ'' : Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
                      (max y (rational δ) · boundedReciprocalPositive δ φ x)
                      (max y (rational δ) · boundedReciprocalPositive δ φ y)
          Φ'' = subst (λ ?ξ → Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ?ξ
                        (max y (rational δ) · boundedReciprocalPositive δ φ x)
                        (max y (rational δ) · boundedReciprocalPositive δ φ y))
                      (ℚ.isProp< 0 (ε ℚ./ 2 [ ℚ.2≠0 ]) (fst Φ') ψ')
                      (snd Φ')

  π : Σ ℚ.ℚ
       (λ η₁ →
          Σ (0 ℚ.< η₁)
          (λ ζ →
             (y : ℝ) →
             Close η₁ ζ x y →
             Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
             (max x (rational δ) · boundedReciprocalPositive δ φ x)
             (max y (rational δ) · boundedReciprocalPositive δ φ x))) →
      Σ ℚ.ℚ
        (λ η₂ →
          Σ (0 ℚ.< η₂)
          (λ ζ →
             (y : ℝ) →
             Close η₂ ζ x y →
             Close (ε ℚ./ 2 [ ℚ.2≠0 ]) ψ'
             (max y (rational δ) · boundedReciprocalPositive δ φ x)
             (max y (rational δ) · boundedReciprocalPositive δ φ y))) →
      Σ ℚ.ℚ
        (λ η →
          Σ (0 ℚ.< η)
          (λ ζ →
             (y : ℝ) →
             Close η ζ x y →
             Close ε ψ (max x (rational δ) · boundedReciprocalPositive δ φ x)
             (max y (rational δ) · boundedReciprocalPositive δ φ y)))
  π (η₁ , ρ₁ , σ₁) (η₂ , ρ₂ , σ₂) = η , ρ , σ
    where
    η : ℚ.ℚ
    η = ℚ.min η₁ η₂

    ρ : 0 ℚ.< η
    ρ = ℚ.minGreatestLowerBound< {η₁} {η₂} {0} ρ₁ ρ₂

    σ : (y : ℝ) →
        Close η ρ x y →
        Close ε ψ
              (max x (rational δ) · boundedReciprocalPositive δ φ x)
              (max y (rational δ) · boundedReciprocalPositive δ φ y)
    σ y τ = υ''
      where
      τ' : distance x y < rational η
      τ' = close→distance< ρ τ 

      υ₁ : distance x y < rational η₁
      υ₁ = <→≤→< {distance x y} {rational η} {rational η₁}
                 τ' (rationalMonotone {η} {η₁} $ ℚ.min≤ η₁ η₂)

      υ₂ : distance x y < rational η₂
      υ₂ = <→≤→< {distance x y} {rational η} {rational η₂}
                 τ' (rationalMonotone {η} {η₂} $ ℚ.min≤' η₁ η₂)

      υ₁' : Close η₁ ρ₁ x y 
      υ₁' = distance<→close ρ₁ υ₁

      υ₂' : Close η₂ ρ₂ x y 
      υ₂' = distance<→close ρ₂ υ₂

      υ : Close ((ε ℚ./ 2 [ ℚ.2≠0 ]) ℚ.+ (ε ℚ./ 2 [ ℚ.2≠0 ]))
                (ℚ.0<+' {ε ℚ./ 2 [ ℚ.2≠0 ]} {ε ℚ./ 2 [ ℚ.2≠0 ]} ψ' ψ')
                (max x (rational δ) · boundedReciprocalPositive δ φ x)
                (max y (rational δ) · boundedReciprocalPositive δ φ y)
      υ = closeTriangleInequality
            (max x (rational δ) · boundedReciprocalPositive δ φ x)
            (max y (rational δ) · boundedReciprocalPositive δ φ x)
            (max y (rational δ) · boundedReciprocalPositive δ φ y)
            (ε ℚ./ 2 [ ℚ.2≠0 ]) (ε ℚ./ 2 [ ℚ.2≠0 ])
            ψ' ψ'
            (σ₁ y υ₁') (σ₂ y υ₂')

      α : (ε ℚ./ 2 [ ℚ.2≠0 ]) ℚ.+ (ε ℚ./ 2 [ ℚ.2≠0 ]) ≡ ε
      α = ℚ.self/2≡self ε ℚ.2≠0

      υ' : Σ (0 ℚ.< ε)
             (λ ξ → Close ε ξ
                      (max x (rational δ) · boundedReciprocalPositive δ φ x)
                      (max y (rational δ) · boundedReciprocalPositive δ φ y))
      υ' = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ _ _))
                 α
                 ((ℚ.0<+' {ε ℚ./ 2 [ ℚ.2≠0 ]} {ε ℚ./ 2 [ ℚ.2≠0 ]} ψ' ψ') , υ)

      υ'' : Close ε ψ
                    (max x (rational δ) · boundedReciprocalPositive δ φ x)
                    (max y (rational δ) · boundedReciprocalPositive δ φ y)
      υ'' = subst (λ ?ξ →
                    Close
                      ε ?ξ
                      (max x (rational δ) · boundedReciprocalPositive δ φ x)
                      (max y (rational δ) · boundedReciprocalPositive δ φ y))
                  (ℚ.isProp< 0 ε (fst υ') ψ)
                  (snd υ')

  ρ : ∃ ℚ.ℚ
      (λ η →
      Σ (0 ℚ.< η)
      (λ ζ →
      (y : ℝ) →
      Close η ζ x y →
      Close ε ψ
            (max x (rational δ) · boundedReciprocalPositive δ φ x)
            (max y (rational δ) · boundedReciprocalPositive δ φ y)))
  ρ = PropositionalTruncation.map2 π ω χ


boundedReciprocalPositiveInverseₗ :
  (δ : ℚ.ℚ) (φ : 0 ℚ.< δ)
  (x : ℝ) →
  max x (rational δ) · boundedReciprocalPositive δ φ x ≡ 1
boundedReciprocalPositiveInverseₗ δ φ =
  continuousExtensionLaw₁
    f g f' g'
    ψ ω χ π ρ
  where
  f : ℝ → ℝ
  f x = max x (rational δ) · boundedReciprocalPositive δ φ x

  g : ℝ → ℝ
  g = const 1

  f' : ℚ.ℚ → ℚ.ℚ
  f' q = ℚ.max q δ ℚ.· boundedReciprocalPositiveRational δ φ q

  g' : ℚ.ℚ → ℚ.ℚ
  g' = const 1

  ψ : (q : ℚ.ℚ) →
      max (rational q) (rational δ) ·
        boundedReciprocalPositive δ φ (rational q) ≡
      rational (ℚ.max q δ ℚ.· boundedReciprocalPositiveRational δ φ q)
  ψ q = max (rational q) (rational δ) ·
          boundedReciprocalPositive δ φ (rational q) 
          ≡⟨ cong (flip _·_ $ boundedReciprocalPositive δ φ (rational q))
                  (maxRational q δ) ⟩
        rational (ℚ.max q δ) · boundedReciprocalPositive δ φ (rational q) 
          ≡⟨ cong (_·_ $ rational (ℚ.max q δ))
                  (boundedReciprocalPositveRational≡boundedReciprocalPositiveRational δ φ q) ⟩
        rational (ℚ.max q δ) ·
          rational (boundedReciprocalPositiveRational δ φ q)
          ≡⟨ multiplyRational (ℚ.max q δ) _ ⟩
        rational (ℚ.max q δ ℚ.· boundedReciprocalPositiveRational δ φ q) ∎

  ω : (q : ℚ.ℚ) → 1 ≡ 1
  ω q = refl

  χ : (q : ℚ.ℚ) →
      ℚ.max q δ ℚ.· boundedReciprocalPositiveRational δ φ q ≡ 1
  χ q = ℚ.⁻¹-inverse (ℚ.max q δ) _

  π : Continuous f
  π = maxMultiplyBoundedReciprocalPositiveContinuous δ φ

  ρ : Continuous g
  ρ = constantContinuous 1

reciprocalPositiveInverseᵣ :
  (x : ℝ) (φ : 0 < x) →
  x · reciprocalPositive x φ ≡ 1
reciprocalPositiveInverseᵣ x φ =
  ∃-rec (ℝ-isSet (x · reciprocalPositive x φ) 1) ω ψ
  where
  ψ : ∃ ℚ.ℚ (λ δ → (0 ℚ.< δ) × (rational δ ≤ x))
  ψ = 0<→existsPositiveRational≤ φ

  ω : (δ : ℚ.ℚ) →
      (0 ℚ.< δ) × (rational δ ≤ x) →
      x · reciprocalPositive x φ ≡ 1
  ω δ (χ , π) =
    x · reciprocalPositive x φ
      ≡⟨ cong (_·_ x) (reciprocalPositive≡boundedReciprocalPositive δ χ x π φ) ⟩
    x · (boundedReciprocalPositive δ χ x)
      ≡⟨ cong (λ ?x → ?x · boundedReciprocalPositive δ χ x)
              (sym $ maxCommutative x (rational δ) ∙ π) ⟩
    (max x (rational δ)) · (boundedReciprocalPositive δ χ x)
      ≡⟨ boundedReciprocalPositiveInverseₗ δ χ x ⟩
    1 ∎

reciprocalInl :
  (x : ℝ) (φ : x < 0) →
  x [ inl φ ]⁻¹ ≡ - reciprocalPositive (- x) (-antitone< {x} {0} φ)
reciprocalInl x φ = refl
                    
reciprocalInr :
  (x : ℝ) (φ : 0 < x) →
  x [ inr φ ]⁻¹ ≡ reciprocalPositive x φ
reciprocalInr x φ = refl

⁻¹-inverseᵣ : (x : ℝ) (φ : x # 0) → x · x [ φ ]⁻¹ ≡ 1
⁻¹-inverseᵣ x (inl φ) =
  cong (_·_ x) (reciprocalInl x φ) ∙ ψ
  where
  ψ = x · (- reciprocalPositive (- x) (-antitone< {x} {0} φ))
        ≡⟨ multiplyNegateRight
             x
             (reciprocalPositive (- x) (-antitone< {x} {0} φ)) ⟩
      - (x · (reciprocalPositive (- x) (-antitone< {x} {0} φ)))
        ≡⟨ (sym $ multiplyNegateLeft
                    x
                    (reciprocalPositive (- x) (-antitone< {x} {0} φ))) ⟩
      (- x) · (reciprocalPositive (- x) (-antitone< {x} {0} φ))
        ≡⟨ reciprocalPositiveInverseᵣ (- x) (-antitone< {x} {0} φ) ⟩
      1 ∎
⁻¹-inverseᵣ x (inr φ) =
  cong (_·_ x) (reciprocalInr x φ) ∙ reciprocalPositiveInverseᵣ x φ

⁻¹-inverseₗ : (x : ℝ) (φ : x # 0) → x [ φ ]⁻¹ · x ≡ 1
⁻¹-inverseₗ x φ =
  x [ φ ]⁻¹ · x
    ≡⟨ ·-commutative (x [ φ ]⁻¹) x ⟩
  x · x [ φ ]⁻¹
    ≡⟨ ⁻¹-inverseᵣ x φ ⟩
  1 ∎
