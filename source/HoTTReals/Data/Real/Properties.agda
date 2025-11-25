module HoTTReals.Data.Real.Properties where

import Cubical.Data.Bool as Bool
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ

-- HoTT Theorem 11.3.9
ℝ-isSet : isSet ℝ
ℝ-isSet = reflPropRelImpliesIdentity→isSet
            (λ x y → (ε : ℚ) (φ : 0 < ε) → x ∼[ ε , φ ] y)
            closeReflexive
            (λ x y → isPropΠ2 (λ ε π → squash ε π x y))
            (λ {x} {y} → path x y)

-- HoTT Lemma 11.3.10
limitSurjective : isSurjection (uncurry limit)
limitSurjective = inductionProposition (φ , ψ , θ)
  where
  φ : (q : ℚ) → ∥ fiber (uncurry limit) (rational q) ∥₁
  φ q = ∣ ((λ ε _ → rational q) , ψ) ,
          path (limit (λ ε _ → rational q) ψ) (rational q) σ ∣₁
    where
    ψ : CauchyApproximation (λ ε _ → rational q)
    ψ ε δ θ ω =
      let π : 0 < ε + δ
          π = 0<+' {x = ε} {y = δ} θ ω

          π' : (q - q) < ε + δ
          π' = subst (λ ?x → ?x < ε + δ) (sym (+InvR q)) π

          ρ : - (ε + δ) < (q - q)
          ρ = subst (λ ?x → - (ε + δ) < ?x)
                    (sym (+InvR q))
                    (<antitone- {x = 0} {y = ε + δ} π)
      in rationalRational q q (ε + δ) (0<+' {x = ε} {y = δ} θ ω) ρ π'

    σ : (ε : ℚ) (τ : 0 < ε) →
        Close ε τ (limit (λ ε₁ _ → rational q) ψ) (rational q)
    σ ε τ =
      let
        υ : ¬ 2 ≡ 0
        υ = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt

        υ' : 0 < 2 [ υ ]⁻¹
        υ' = Bool.toWitness {Q = <Dec 0 (2 [ υ ]⁻¹)} tt

        α : 0 < ε / 2 [ υ ]
        α = subst (λ ?x → ?x < ε / 2 [ υ ])
                  (·AnnihilR (2 [ υ ]⁻¹))
                  (<-·o 0 ε (2 [ υ ]⁻¹) υ' τ)

        β = ε - (ε / 2 [ υ ]) ≡ ε / 2 [ υ ]
        β =
          ε - (ε / 2 [ υ ])
            ≡⟨ cong (λ ?x → ?x - (ε / 2 [ υ ])) (sym (·IdR ε)) ⟩
          (ε · 1) - (ε · 2 [ υ ]⁻¹)
            ≡⟨ cong (λ ?x → (ε · 1) + ?x) (-·≡·- ε (2 [ υ ]⁻¹)) ⟩
          (ε · 1) + (ε · (- (2 [ υ ]⁻¹)))
            ≡⟨ sym (·DistL+ ε 1 (- (2 [ υ ]⁻¹))) ⟩
          ε · (1 + (- (2 [ υ ]⁻¹)))
            ≡⟨ refl ⟩
          ε / 2 [ υ ] ∎

        α' : 0 < ε - (ε / 2 [ υ ])
        α' = subst (λ ?x → 0 < ?x) (sym β) α

        γ : q - q < ε - (ε / 2 [ υ ])
        γ = subst (λ ?x → ?x < ε - (ε / 2 [ υ ])) (sym (+InvR q)) α'

        γ' : - (ε - (ε / 2 [ υ ])) < q - q
        γ' =
          subst (λ ?x → - (ε - (ε / 2 [ υ ])) < ?x)
                (sym (+InvR q))
                (<antitone- {x = 0} {y = ε - (ε / 2 [ υ ])} α')
      in limitRational
           (λ ε _ → rational q) ψ
           q
           ε (ε / 2 [ υ ])
           τ α
           α' (rationalRational q q (ε - (ε / 2 [ υ ])) α' γ' γ)

  ψ : (x : (ε : ℚ) → 0 < ε → ℝ) (θ : CauchyApproximation x) →
      ((ε : ℚ) (ψ : 0 < ε) → ∥ fiber (uncurry limit) (x ε ψ) ∥₁) →
      ∥ fiber (uncurry limit) (limit x θ) ∥₁
  ψ x θ _ = ∣ ((x , θ) , refl) ∣₁

  θ : (x : ℝ) → isProp ∥ fiber (uncurry limit) x ∥₁
  θ _ = isPropPropTrunc

continuousProposition : (f : ℝ → ℝ) → isProp (Continuous f)
continuousProposition f = isPropΠ3 (λ _ _ _ → isPropPropTrunc)

continuousExtensionUnique :
  (f g : ℝ → ℝ) (φ : Continuous f) (ψ : Continuous g) →
  ((q : ℚ) → f (rational q) ≡ g (rational q)) →
  ((u : ℝ) → f u ≡ g u)
continuousExtensionUnique f g φ ψ ω =
  inductionProposition (θ , χ , π)
  where
  θ : (q : ℚ) → f (rational q) ≡ g (rational q)
  θ = ω

  χ : (x : (ε : ℚ) → 0 < ε → ℝ) (π : CauchyApproximation x) →
      ((ε : ℚ) (ρ : 0 < ε) → f (x ε ρ) ≡ g (x ε ρ)) →
      f (limit x π) ≡ g (limit x π)
  χ x π ρ = path (f (limit x π)) (g (limit x π)) χ'
    where
    2≠0 : ¬ 2 ≡ 0
    2≠0 = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt

    0<2 : 0 < 2
    0<2 = Bool.toWitness {Q = <Dec 0 2} tt

    χ' : (ε : ℚ) (ρ : 0 < ε) → Close ε ρ (f (limit x π)) (g (limit x π))
    χ' ε σ =
      ∃-rec
        (squash ε σ (f (limit x π)) (g (limit x π)))
        (∃-rec
          (isPropΠ2 (λ _ _ → squash ε σ (f (limit x π)) (g (limit x π))))
          χ''
          (ψ (limit x π) (ε / 2 [ 2≠0 ]) (0</ {x = ε} {y = 2} σ 0<2)))
        (φ (limit x π) (ε / 2 [ 2≠0 ]) (0</ {x = ε} {y = 2} σ 0<2))
      where
      χ'' : (θ : ℚ) →
            Σ (0 < θ)
            (λ τ →
            (v : ℝ) →
            Close θ τ (limit x π) v →
            Close (ε / 2 [ 2≠0 ]) (0</ {x = ε} {y = 2} σ 0<2)
                  (g (limit x π)) (g v)) →
            (η : ℚ) →
            Σ (0 < η)
            (λ υ →
            (v : ℝ) →
            Close η υ (limit x π) v →
            Close (ε / 2 [ 2≠0 ]) (0</ {x = ε} {y = 2} σ 0<2)
                  (f (limit x π)) (f v)) →
            Close ε σ (f (limit x π)) (g (limit x π))
      χ'' θ (τ , υ) η (ξ , ο) =
        let
          δ : ℚ
          δ = (min θ η) / 2 [ 2≠0 ]

          bar : 0 < min θ η
          bar = minGreatestLowerBound< {θ} {η} {0} τ ξ

          α : 0 < δ
          α = 0</ {x = min θ η} {y = 2} bar 0<2

          foo' : (min θ η) / 2 [ 2≠0 ] < min θ η
          foo' =
            subst
              (_<_ ((min θ η) / 2 [ 2≠0 ]))
              (·IdR (min θ η))
              (≤→<→·<· {min θ η} {2 [ 2≠0 ]⁻¹} {min θ η} {1}
                       (isRefl≤ (min θ η))
                       (Bool.toWitness {Q = <Dec (2 [ 2≠0 ]⁻¹) 1} tt)
                       bar
                       (Bool.toWitness {Q = ≤Dec 0 (2 [ 2≠0 ]⁻¹)} tt)) 

          foo : 0 < θ - δ 
          foo = <→0<- {δ} {θ} (isTrans<≤ δ (min θ η) θ foo' (min≤ θ η))

          baz : 0 < η - δ
          baz = <→0<- {δ} {η} (isTrans<≤ δ (min θ η) η foo' (min≤' θ η))

          buzz' : Close ((η - δ) + δ) (0<+' {η - δ} {δ} baz α)
                        (limit x π) (x δ α)
          buzz' =
            closeSymmetric
              (x δ α)
              (limit x π)
              ((η - δ) + δ) (0<+' {η - δ} {δ} baz α)
              (closeLimit'' x π δ (η - δ) α baz)

          buzz : Σ (0 < η)
                   (λ half → Close η half (limit x π) (x δ α))
          buzz = subst (λ ?x → Σ (0 < ?x)
                                 (λ half → Close ?x half (limit x π) (x δ α)))
                       (subtractAddRightCancel δ η)
                       ((0<+' {η - δ} {δ} baz α) , buzz')

          buzz'' : Close η ξ (limit x π) (x δ α)
          buzz'' = subst (λ ?x → Close η ?x (limit x π) (x δ α))
                         (isProp< 0 η (fst buzz) ξ)
                         (snd buzz)

          β : Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                    (f (limit x π)) (f (x δ α))
          β = ο (x δ α) buzz''

          meal'' : Close ((θ - δ) + δ) (0<+' {θ - δ} {δ} foo α)
                         (limit x π) (x δ α)
          meal'' =
            closeSymmetric
              (x δ α) (limit x π) ((θ - δ) + δ) (0<+' {θ - δ} {δ} foo α)
              (closeLimit'' x π δ (θ - δ) α foo)

          meal' : Σ (0 < θ)
                    (λ hash → Close θ hash (limit x π) (x δ α))
          meal' = subst (λ ?x → Σ (0 < ?x)
                                  (λ hash → Close ?x hash (limit x π) (x δ α)))
                        (subtractAddRightCancel δ θ)
                        ((0<+' {θ - δ} {δ} foo α) , meal'')

          meal : Close θ τ (limit x π) (x δ α)
          meal = subst (λ ?x → Close θ ?x (limit x π) (x δ α))
                       (isProp< 0 θ (fst meal') τ)
                       (snd meal')

          monster : Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                          (g (limit x π)) (g (x δ α))
          monster = υ (x δ α) meal

          car : Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                      (f (x δ α)) (g (limit x π))
          car = subst (λ ?x → Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2) ?x _)
                      (sym $ ρ δ α)
                      (closeSymmetric
                        (g (limit x π)) (g (x δ α))
                        (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                        monster)

          curse : Close ((ε / 2 [ 2≠0 ]) + (ε / 2 [ 2≠0 ]))
                        (0<+' {ε / 2 [ 2≠0 ]} {ε / 2 [ 2≠0 ]}
                          (0</ {ε} {2} σ 0<2) (0</ {ε} {2} σ 0<2))
                        (f (limit x π)) (g (limit x π))
          curse =
            closeTriangleInequality
              (f (limit x π)) (f (x δ α)) (g (limit x π))
              (ε / 2 [ 2≠0 ]) (ε / 2 [ 2≠0 ])
              (0</ {ε} {2} σ 0<2) (0</ {ε} {2} σ 0<2)
              β car

          curse' : Σ (0 < ε)
                   (λ mask → Close ε mask (f (limit x π)) (g (limit x π)))
          curse' =
            subst (λ ?x → Σ (0 < ?x)
                            (λ mask → Close ?x mask
                                            (f (limit x π)) (g (limit x π))))
                  (self/2≡self ε 2≠0)
                  (((0<+' {ε / 2 [ 2≠0 ]} {ε / 2 [ 2≠0 ]}
                          (0</ {ε} {2} σ 0<2) (0</ {ε} {2} σ 0<2))) ,
                   curse)

          curse'' : Close ε σ (f (limit x π)) (g (limit x π))
          curse'' = subst (λ ?x → Close ε ?x (f (limit x π)) (g (limit x π)))
                          (isProp< 0 ε (fst curse') σ)
                          (snd curse')
        in curse''

  π : (u : ℝ) → isProp (f u ≡ g u)
  π u = ℝ-isSet (f u) (g u)
  
