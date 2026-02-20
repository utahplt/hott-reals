module HoTTReals.Data.Real.Algebra.Reciprocal where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
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
open import HoTTReals.Data.Real.Order.Properties.Properties1
open import HoTTReals.Data.Real.Order.Properties.Properties2

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

reciprocalMaxLipschitzℚ : 
  (δ : ℚ.ℚ) (φ : 0 ℚ.< δ) →
  let ψ : ¬ δ ≡ 0
      ψ = ≠-symmetric $ ℚ.<→≠ φ

      φ' : 0 ℚ.< δ ℚ.· δ
      φ' = ℚ.0<· {x = δ} {y = δ} φ φ

      ψ' : ¬ δ ℚ.· δ ≡ 0
      ψ' = ≠-symmetric $ ℚ.<→≠ φ'

      φ'' : 0 ℚ.< (δ ℚ.· δ) [ ψ' ]⁻¹
      φ'' = ℚ.0<⁻¹' {x = δ ℚ.· δ} φ'
  in 
  Lipschitzℚ
    (λ q →
      let ω : 0 ℚ.< ℚ.max q δ
          ω = ℚ.isTrans<≤ 0 δ (ℚ.max q δ) φ (ℚ.≤max' q δ)

          ω' : ¬ ℚ.max q δ ≡ 0
          ω' = ≠-symmetric $ ℚ.<→≠ ω
      in rational $ (ℚ.max q δ) [ ω' ]⁻¹) ((δ ℚ.· δ) [ ψ' ]⁻¹) φ''
reciprocalMaxLipschitzℚ δ φ q r ε χ π = γ''
  where
  ψ : ¬ δ ≡ 0
  ψ = ≠-symmetric $ ℚ.<→≠ φ

  φ' : 0 ℚ.< δ ℚ.· δ
  φ' = ℚ.0<· {x = δ} {y = δ} φ φ

  ψ' : ¬ δ ℚ.· δ ≡ 0
  ψ' = ≠-symmetric $ ℚ.<→≠ φ'

  φ'' : 0 ℚ.< (δ ℚ.· δ) [ ψ' ]⁻¹
  φ'' = ℚ.0<⁻¹' {x = δ ℚ.· δ} φ'

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

  τ'' : 0 ℚ.< (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹
  τ'' = ℚ.0<⁻¹' {x = ℚ.max q δ ℚ.· ℚ.max r δ} τ

  υ : δ ℚ.· δ ℚ.≤ ℚ.max q δ ℚ.· ℚ.max r δ
  υ = ℚ.·≤· {x = δ} {y = δ} {z = ℚ.max q δ} {w = ℚ.max r δ}
            (ℚ.≤max' q δ) (ℚ.≤max' r δ)
            (ℚ.<Weaken≤ 0 (ℚ.max q δ) ω) (ℚ.<Weaken≤ 0 δ φ)

  υ' : ((ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹) ℚ.≤ ((δ ℚ.· δ) [ ψ' ]⁻¹)
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
  α'' = rationalStrictReflective {q = ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣} {r = ε} α'

  β : ℚ.∣ ((ℚ.max q δ) [ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣ ≡
        (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹ ℚ.· ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣
  β = ℚ.∣ ((ℚ.max q δ) [ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ?x ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣)
                (sym $ ℚ.·IdR $ (ℚ.max q δ) [ ω' ]⁻¹) ⟩
      ℚ.∣ (((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· 1) ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ (((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ?x) ℚ.-
                            ((ℚ.max r δ) [ σ' ]⁻¹) ∣)
                (sym $ ⁻¹-inverse' (ℚ.max r δ) σ') ⟩
      ℚ.∣ (((ℚ.max q δ) [ ω' ]⁻¹) ℚ.·
           (((ℚ.max r δ) [ σ' ]⁻¹) ℚ.· (ℚ.max r δ))) ℚ.-
          ((ℚ.max r δ) [ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ?x ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣)
                (ℚ.·Assoc ((ℚ.max q δ) [ ω' ]⁻¹)
                          (ℚ.max r δ [ σ' ]⁻¹)
                          (ℚ.max r δ)) ⟩
      ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
           (ℚ.max r δ)) ℚ.-
          ((ℚ.max r δ) [ σ' ]⁻¹) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.·
                              ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
                             (ℚ.max r δ)) ℚ.- ?x ∣)
                (sym $ ℚ.·IdR $ (ℚ.max r δ) [ σ' ]⁻¹) ⟩
      ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
           (ℚ.max r δ)) ℚ.-
          (((ℚ.max r δ) [ σ' ]⁻¹) ℚ.· 1) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.·
                              ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
                             (ℚ.max r δ)) ℚ.-
                            (((ℚ.max r δ) [ σ' ]⁻¹) ℚ.· ?x) ∣)
                (sym $ ⁻¹-inverse' (ℚ.max q δ) ω') ⟩
      ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
           (ℚ.max r δ)) ℚ.-
          (((ℚ.max r δ) [ σ' ]⁻¹) ℚ.·
           (((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· (ℚ.max q δ))) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.·
                              ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
                             (ℚ.max r δ)) ℚ.-
                            ?x ∣)
                (ℚ.·Assoc (((ℚ.max r δ) [ σ' ]⁻¹))
                          (ℚ.max q δ [ ω' ]⁻¹)
                          (ℚ.max q δ)) ⟩
      ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
           (ℚ.max r δ)) ℚ.-
          ((((ℚ.max r δ) [ σ' ]⁻¹) ℚ.· ((ℚ.max q δ) [ ω' ]⁻¹)) ℚ.·
           (ℚ.max q δ)) ∣
        ≡⟨ cong (λ ?x → ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.·
                              ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
                             (ℚ.max r δ)) ℚ.-
                            (?x ℚ.· (ℚ.max q δ)) ∣)
                (ℚ.·Comm (ℚ.max r δ [ σ' ]⁻¹)
                         (ℚ.max q δ [ ω' ]⁻¹)) ⟩
      ℚ.∣ ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
           (ℚ.max r δ)) ℚ.-
          ((((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ℚ.·
           (ℚ.max q δ)) ∣
        ≡⟨ ℚ.·distanceₗ (((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹))
                        (ℚ.max r δ)
                        (ℚ.max q δ) ⟩
      ℚ.∣ (((ℚ.max q δ) [ ω' ]⁻¹) ℚ.· ((ℚ.max r δ) [ σ' ]⁻¹)) ∣ ℚ.·
      ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣
        ≡⟨ cong (λ ?x → (ℚ.∣ ?x ∣) ℚ.· (ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣))
                (sym $ ℚ.·⁻¹' (ℚ.max q δ) (ℚ.max r δ) ω' σ' τ') ⟩
      ℚ.∣ (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹ ∣ ℚ.·
      ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣
        ≡⟨ cong (flip ℚ._·_ $ ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣)
                (ℚ.0≤→∣∣≡self
                  (((ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹))
                  (ℚ.<Weaken≤ 0 ((ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹) τ'') ) ⟩
      ((ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹) ℚ.·
      ℚ.∣ (ℚ.max r δ) ℚ.- (ℚ.max q δ) ∣
        ≡⟨ cong (ℚ._·_ $ (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹)
                (ℚ.distanceCommutative (ℚ.max r δ) (ℚ.max q δ)) ⟩
      (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹ ℚ.· ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣ ∎

  γ : (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹ ℚ.· ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣ ℚ.<
      ((δ ℚ.· δ) [ ψ' ]⁻¹) ℚ.· ε
  γ = ℚ.≤→<→·<·
        {x = (ℚ.max q δ ℚ.· ℚ.max r δ) [ τ' ]⁻¹}
        {y = ℚ.∣ ℚ.max q δ ℚ.- ℚ.max r δ ∣}
        {z = (δ ℚ.· δ) [ ψ' ]⁻¹}
        {w = ε}
        υ' α''
        φ''
        (ℚ.0≤∣∣ $ ℚ.max q δ ℚ.- ℚ.max r δ)

  γ' : ℚ.∣ ((ℚ.max q δ) [ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣ ℚ.<
       ((δ ℚ.· δ) [ ψ' ]⁻¹) ℚ.· ε
  γ' = subst (flip ℚ._<_ $ ((δ ℚ.· δ) [ ψ' ]⁻¹) ℚ.· ε)
             (sym β)
             γ

  γ'' : Close
          (((δ ℚ.· δ) [ ψ' ]⁻¹) ℚ.· ε)
          (ℚ.0<· {x = (δ ℚ.· δ) [ ψ' ]⁻¹} {y = ε} φ'' χ)
          (rational ((ℚ.max q δ) [ ω' ]⁻¹))
          (rational ((ℚ.max r δ) [ σ' ]⁻¹))
  γ'' = distance<→close
          _
          (rationalStrictMonotone
            {q = ℚ.∣ ((ℚ.max q δ) [ ω' ]⁻¹) ℚ.- ((ℚ.max r δ) [ σ' ]⁻¹) ∣}
            {r = ((δ ℚ.· δ) [ ψ' ]⁻¹) ℚ.· ε}
            γ')

-- boundedReciprocal :
--   (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) →
--   ℝ → ℝ
-- boundedReciprocal ε φ = {!!}

