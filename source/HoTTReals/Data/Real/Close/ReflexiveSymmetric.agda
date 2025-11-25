module HoTTReals.Data.Real.Close.ReflexiveSymmetric where

import Cubical.Data.Bool as Bool
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Induction

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ

-- HoTT Lemma 11.3.8
closeReflexive :
  BinaryRelation.isRefl (λ x y → (ε : ℚ) (φ : 0 < ε) → x ∼[ ε , φ ] y)
closeReflexive u = inductionProposition (ψ , θ , ω) u
  where
  ψ : ((q : ℚ) → ((ε : ℚ) (φ : 0 < ε) → rational q ∼[ ε , φ ] rational q))
  ψ q ε φ = rationalRational
          q q ε φ
          (let θ : q - q ≡ - 0
               θ = q - q ≡⟨ +InvR q ⟩ 0
                         ≡⟨ refl ⟩ - 0 ∎

               ω : - ε < - 0
               ω = <antitone- {x = 0} {y = ε} φ
           in subst (λ ?x → - ε < ?x) (sym θ) ω)
          (subst (λ ?x → ?x < ε) (sym (+InvR q)) φ)

  θ : (x : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation x) →
      ((δ : ℚ) (π : 0 < δ) → ((ε : ℚ) (ρ : 0 < ε) → x δ π ∼[ ε , ρ ] x δ π)) →
      ((ε : ℚ) (π : 0 < ε) → limit x ω ∼[ ε , π ] limit x ω)
  θ x ω π ε ρ =
    let σ : ¬ 3 ≡ 0
        σ = Bool.toWitnessFalse {Q = discreteℚ 3 0} tt

        τ' : 0 < 3 [ σ ]⁻¹
        τ' = Bool.toWitness {Q = <Dec 0 (3 [ σ ]⁻¹)} tt

        τ : 0 < ε / 3 [ σ ]
        -- TODO: Perphaps pull out into lemma for division
        τ = subst (λ ?x → ?x < (ε / 3 [ σ ]))
                  (·AnnihilR (3 [ σ ]⁻¹))
                  (<-·o 0 ε (3 [ σ ]⁻¹) τ' ρ)

        υ' : (ε / 3 [ σ ] + ε / 3 [ σ ]) ≡ (2 / 3 [ σ ]) · ε
        υ' =
            ε / 3 [ σ ] + ε / 3 [ σ ]
              ≡⟨ sym (·DistR+ ε ε (3 [ σ ]⁻¹)) ⟩
            (ε + ε) · (3 [ σ ]⁻¹)
              ≡⟨ cong (λ ?x → ?x · (3 [ σ ]⁻¹)) (self+≡2· ε) ⟩
            (2 · ε) · (3 [ σ ]⁻¹)
              ≡⟨ sym (·Assoc 2 ε (3 [ σ ]⁻¹)) ⟩
            2 · (ε · (3 [ σ ]⁻¹))
              ≡⟨ cong (λ ?x → 2 · ?x) (·Comm ε (3 [ σ ]⁻¹)) ⟩
            2 · ((3 [ σ ]⁻¹) · ε)
              ≡⟨ ·Assoc 2 (3 [ σ ]⁻¹) ε ⟩
            (2 · (3 [ σ ]⁻¹)) · ε
              ≡⟨ refl ⟩
            (2 / 3 [ σ ]) · ε ∎

        υ : ε - (ε / 3 [ σ ] + ε / 3 [ σ ]) ≡ ε / 3 [ σ ]
        υ =
          ε - (ε / 3 [ σ ] + ε / 3 [ σ ])
            ≡⟨ cong (λ ?x → ε - ?x) υ' ⟩
          ε + (- ((2 / 3 [ σ ]) · ε))
            ≡⟨ cong (λ ?x → ε + ?x) (-·≡-· (2 / 3 [ σ ]) ε) ⟩
          ε + ((- 2) / 3 [ σ ]) · ε
            ≡⟨ cong (λ ?x → ?x + ((- 2) / 3 [ σ ]) · ε) (sym (·IdL ε)) ⟩
          1 · ε + ((- 2) / 3 [ σ ]) · ε
            ≡⟨ sym (·DistR+ 1 ((- 2) / 3 [ σ ]) ε) ⟩
          (1 - (2 / 3 [ σ ])) · ε
            ≡⟨ refl ⟩
          (3 [ σ ]⁻¹) · ε
            ≡⟨ ·Comm (3 [ σ ]⁻¹) ε ⟩
          ε / 3 [ σ ] ∎

        ι : 0 < ε - (ε / 3 [ σ ] + ε / 3 [ σ ])
        ι = subst (λ ?x → 0 < ?x) (sym υ) τ

        κ : Close (ε - ((ε / 3 [ σ ]) + (ε / 3 [ σ ]))) ι
                  (x (ε / 3 [ σ ]) τ) (x (ε / 3 [ σ ]) τ)
        κ = π (ε / 3 [ σ ]) τ (ε - ((ε / 3 [ σ ]) + (ε / 3 [ σ ]))) ι
    in limitLimit
         x x ω ω
         ε (ε / 3 [ σ ]) (ε / 3 [ σ ]) ρ τ τ ι
         κ

  ω : (u : ℝ) → isProp ((ε : ℚ) (π : 0 < ε) → u ∼[ ε , π ] u)
  ω u = isPropΠ2 (λ ε π → squash ε π u u)

-- HoTT Lemma 11.3.12
closeSymmetric :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v → v ∼[ ε , φ ] u
closeSymmetric _ _ _ _ =
  induction∼ {B = λ {u} {v} {ε} {φ} _ → (v ∼[ ε , φ ] u)} (φ , ψ , θ , ω , χ)
  where
  φ : (q r ε : ℚ) (ψ : 0 < ε) →
      (- ε) < q - r → q - r < ε →
      (rational r) ∼[ ε , ψ ] (rational q)
  φ q r ε ψ ω θ = rationalRational r q ε ψ χ π
    where
    α : - (q - r) ≡ r - q
    α = - (q - r)
          ≡⟨ negateSubtract q r ⟩
        - q + r
          ≡⟨ +Comm (- q) r ⟩
        r - q ∎

    χ : - ε < r - q
    χ = subst (λ ?x → - ε < ?x) α (<antitone- {x = q - r} {y = ε} θ)

    π : r - q < ε 
    π = subst2 (λ ?y ?x → ?y < ?x)
               α (-Invol ε)
               (<antitone- {x = - ε} {y = q - r} ω)

  ψ : (q δ ε : ℚ) (φ : 0 < δ) (ψ : 0 < ε) (θ : 0 < ε - δ)
      (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) →
      (rational q) ∼[ (ε - δ) , θ ] (y δ φ) →
      (y δ φ) ∼[ (ε - δ) , θ ] (rational q) →
      (limit y ω) ∼[ ε , ψ ] (rational q)
  ψ q δ ε φ ψ θ y ω π ρ = limitRational y ω q ε δ ψ φ θ ρ

  θ : (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
      (r δ ε : ℚ) (ψ : 0 < δ) (θ : 0 < ε) (ω : 0 < ε - δ) →
      (x δ ψ) ∼[ (ε - δ) , ω ] (rational r) →
      (rational r) ∼[ (ε - δ) , ω ] (x δ ψ) →
      (rational r) ∼[ ε , θ ]  (limit x φ)
  θ x φ r δ ε ψ θ ω π ρ = rationalLimit r ε δ θ ψ ω x φ ρ

  ω : (x y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
      (ψ : CauchyApproximation y) (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ)
      (π : 0 < η) (ρ : 0 < ε - (δ + η)) →
      (x δ ω) ∼[ ε - (δ + η) , ρ ] (y η π) →
      (y η π) ∼[ ε - (δ + η) , ρ ] (x δ ω) →
      (limit y ψ) ∼[ ε , θ ] (limit x φ)
  ω x y φ ψ ε δ η θ ω π ρ σ τ =
    let υ : Σ (0 < ε - (η + δ)) (λ α → y η π ∼[ ε - (η + δ) , α ] x δ ω)
        υ = subst (λ ?x → Σ (0 < (ε - ?x))
                            (λ α → y η π ∼[ ε - ?x , α ] x δ ω))
                  (+Comm δ η)
                  (ρ , τ)
    in limitLimit y x ψ φ ε η δ θ π ω (fst υ) (snd υ)

  χ : (u v : ℝ) (ε : ℚ) (φ : 0 < ε) (ψ : u ∼[ ε , φ ] v) →
      isProp (v ∼[ ε , φ ] u)
  χ u v ε φ ψ = squash ε φ v u

closeSymmetric' :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v ≃ v ∼[ ε , φ ] u
closeSymmetric' u v ε φ =
  propBiimpl→Equiv
    (squash ε φ u v)
    (squash ε φ v u)
    (closeSymmetric u v ε φ)
    (closeSymmetric v u ε φ)

closeSymmetric'' :
  (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → u ∼[ ε , φ ] v ≡ v ∼[ ε , φ ] u
closeSymmetric'' u v ε φ = ua (closeSymmetric' u v ε φ)
