module HoTTReals.Data.Real.Algebra.Reciprocal where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Nat.Literals public
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

boundedReciprocalPositive-inverseₗ :
  (δ : ℚ.ℚ) (φ : 0 ℚ.< δ)
  (x : ℝ) →
  max x (rational δ) · boundedReciprocalPositive δ φ x ≡ 1
boundedReciprocalPositive-inverseₗ δ φ =
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
          ≡⟨ {!!} ⟩
        rational (ℚ.max q δ) · boundedReciprocalPositive δ φ (rational q) 
          ≡⟨ {!!} ⟩
        rational (ℚ.max q δ) ·
          rational (boundedReciprocalPositiveRational δ φ q)
          ≡⟨ {!!} ⟩
        rational (ℚ.max q δ ℚ.· boundedReciprocalPositiveRational δ φ q) ∎

  ω : (q : ℚ.ℚ) → 1 ≡ 1
  ω q = refl

  χ : (q : ℚ.ℚ) →
      ℚ.max q δ ℚ.· boundedReciprocalPositiveRational δ φ q ≡ 1
  χ q = ℚ.⁻¹-inverse (ℚ.max q δ) _

  π : Continuous f
  π = {!!}

  ρ : Continuous g
  ρ = {!!}
