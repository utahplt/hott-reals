module HoTTReals.Data.Real.Properties where

import Cubical.Data.Bool as Bool
open import Cubical.Data.Rationals as ℚ hiding (_∼_)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Nonexpanding

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

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
  ((f ∘ rational) ∼ (g ∘ rational)) →
  f ∼ g
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
      χ'' θ (τ , υ) η (ξ , ο) = ϕ''
        where
        δ : ℚ
        δ = (min θ η) / 2 [ 2≠0 ]

        α : 0 < min θ η
        α = minGreatestLowerBound< {θ} {η} {0} τ ξ

        α' : 0 < δ
        α' = 0</ {x = min θ η} {y = 2} α 0<2

        β : (min θ η) / 2 [ 2≠0 ] < min θ η
        β =
          subst
            (_<_ ((min θ η) / 2 [ 2≠0 ]))
            (·IdR (min θ η))
            (≤→<→·<· {min θ η} {2 [ 2≠0 ]⁻¹} {min θ η} {1}
                     (isRefl≤ (min θ η))
                     (Bool.toWitness {Q = <Dec (2 [ 2≠0 ]⁻¹) 1} tt)
                     α
                     (Bool.toWitness {Q = ≤Dec 0 (2 [ 2≠0 ]⁻¹)} tt)) 

        γ : 0 < θ - δ 
        γ = <→0<- {δ} {θ} (isTrans<≤ δ (min θ η) θ β (min≤ θ η))

        γ' : 0 < η - δ
        γ' = <→0<- {δ} {η} (isTrans<≤ δ (min θ η) η β (min≤' θ η))

        ζ : Close ((η - δ) + δ) (0<+' {η - δ} {δ} γ' α')
                  (limit x π) (x δ α')
        ζ =
          closeSymmetric
            (x δ α')
            (limit x π)
            ((η - δ) + δ) (0<+' {η - δ} {δ} γ' α')
            (closeLimit'' x π δ (η - δ) α' γ')

        ζ' : Σ (0 < η)
               (λ ι → Close η ι (limit x π) (x δ α'))
        ζ' = subst (λ ?x → Σ (0 < ?x)
                               (λ ι → Close ?x ι (limit x π) (x δ α')))
                     (subtractAddRightCancel δ η)
                     ((0<+' {η - δ} {δ} γ' α') , ζ)

        ζ'' : Close η ξ (limit x π) (x δ α')
        ζ'' = subst (λ ?x → Close η ?x (limit x π) (x δ α'))
                       (isProp< 0 η (fst ζ') ξ)
                       (snd ζ')

        ι : Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                  (f (limit x π)) (f (x δ α'))
        ι = ο (x δ α') ζ''

        κ : Close ((θ - δ) + δ) (0<+' {θ - δ} {δ} γ α')
                  (limit x π) (x δ α')
        κ =
          closeSymmetric
            (x δ α') (limit x π) ((θ - δ) + δ) (0<+' {θ - δ} {δ} γ α')
            (closeLimit'' x π δ (θ - δ) α' γ)

        κ' : Σ (0 < θ)
               (λ μ → Close θ μ (limit x π) (x δ α'))
        κ' = subst (λ ?x → Σ (0 < ?x)
                                (λ μ → Close ?x μ (limit x π) (x δ α')))
                      (subtractAddRightCancel δ θ)
                      ((0<+' {θ - δ} {δ} γ α') , κ)

        κ'' : Close θ τ (limit x π) (x δ α')
        κ'' = subst (λ ?x → Close θ ?x (limit x π) (x δ α'))
                     (isProp< 0 θ (fst κ') τ)
                     (snd κ')

        μ : Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                  (g (limit x π)) (g (x δ α'))
        μ = υ (x δ α') κ''

        ν : Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                    (f (x δ α')) (g (limit x π))
        ν = subst (λ ?x → Close (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2) ?x _)
                    (sym $ ρ δ α')
                    (closeSymmetric
                      (g (limit x π)) (g (x δ α'))
                      (ε / 2 [ 2≠0 ]) (0</ {ε} {2} σ 0<2)
                      μ)

        ϕ : Close ((ε / 2 [ 2≠0 ]) + (ε / 2 [ 2≠0 ]))
                  (0<+' {ε / 2 [ 2≠0 ]} {ε / 2 [ 2≠0 ]}
                    (0</ {ε} {2} σ 0<2) (0</ {ε} {2} σ 0<2))
                  (f (limit x π)) (g (limit x π))
        ϕ =
          closeTriangleInequality
            (f (limit x π)) (f (x δ α')) (g (limit x π))
            (ε / 2 [ 2≠0 ]) (ε / 2 [ 2≠0 ])
            (0</ {ε} {2} σ 0<2) (0</ {ε} {2} σ 0<2)
            ι ν

        ϕ' : Σ (0 < ε)
             (λ mask → Close ε mask (f (limit x π)) (g (limit x π)))
        ϕ' =
          subst (λ ?x → Σ (0 < ?x)
                          (λ mask → Close ?x mask
                                          (f (limit x π)) (g (limit x π))))
                (self/2≡self ε 2≠0)
                (((0<+' {ε / 2 [ 2≠0 ]} {ε / 2 [ 2≠0 ]}
                        (0</ {ε} {2} σ 0<2) (0</ {ε} {2} σ 0<2))) ,
                 ϕ)

        ϕ'' : Close ε σ (f (limit x π)) (g (limit x π))
        ϕ'' = subst (λ ?x → Close ε ?x (f (limit x π)) (g (limit x π)))
                        (isProp< 0 ε (fst ϕ') σ)
                        (snd ϕ')

  π : (u : ℝ) → isProp (f u ≡ g u)
  π u = ℝ-isSet (f u) (g u)

continuousExtensionUnique₂ : 
  (f g : ℝ → ℝ → ℝ) →
  ((u : ℝ) → Continuous $ f u) → ((u : ℝ) → Continuous $ g u) →
  ((v : ℝ) → Continuous $ flip f v) → ((v : ℝ) → Continuous $ flip g v) →
  ((q r : ℚ) → f (rational q) (rational r) ≡ g (rational q) (rational r)) →
  ((u v : ℝ) → f u v ≡ g u v)
continuousExtensionUnique₂ f g φ ψ ω χ π u =
  ρ σ
  where
  ρ : ((q : ℚ) → f u (rational q) ≡ g u (rational q)) →
      (v : ℝ) → f u v ≡ g u v
  ρ = continuousExtensionUnique (f u) (g u) (φ u) (ψ u)

  σ : (q : ℚ) → f u (rational q) ≡ g u (rational q)
  σ q = continuousExtensionUnique
          (flip f $ rational q) (flip g $ rational q)
          (ω $ rational q) (χ $ rational q)
          (flip π q)
          u

continuousExtensionUnique₃ : 
  (f g : ℝ → ℝ → ℝ → ℝ) →
  ((u v : ℝ) → Continuous (λ w → f u v w)) →
  ((u w : ℝ) → Continuous (λ v → f u v w)) →
  ((v w : ℝ) → Continuous (λ u → f u v w)) →
  ((u v : ℝ) → Continuous (λ w → g u v w)) →
  ((u w : ℝ) → Continuous (λ v → g u v w)) →
  ((v w : ℝ) → Continuous (λ u → g u v w)) →
  ((q r s : ℚ) →
   f (rational q) (rational r) (rational s) ≡
   g (rational q) (rational r) (rational s)) →
  ((u v w : ℝ) → f u v w ≡ g u v w)
continuousExtensionUnique₃ f g φ ψ ω χ π ρ σ u v =
  τ υ
  where
  τ : ((s : ℚ) → f u v (rational s) ≡ g u v (rational s)) →
      (w : ℝ) → f u v w ≡ g u v w
  τ = continuousExtensionUnique (f u v) (g u v) (φ u v) (χ u v)

  υ : (s : ℚ) → f u v (rational s) ≡ g u v (rational s)
  υ s = continuousExtensionUnique₂
          (λ u v → f u v $ rational s) (λ u v → g u v $ rational s)
          (flip ψ $ rational s)
          (flip π $ rational s)
          (flip ω $ rational s)
          (flip ρ $ rational s)
          (λ q r → σ q r s) u v
  
lipschitz→continuous :
  (f : ℝ → ℝ) (L : ℚ) (φ : 0 < L) → 
  Lipschitzℝ f L φ →
  Continuous f
lipschitz→continuous f L φ ψ u ε ω =
  ∣ ε / L [ L≠0 ] , (χ , (λ v π → ρ v $ ψ u v (ε / L [ L≠0 ]) χ π)) ∣₁
  where
  L≠0 : ¬ L ≡ 0
  L≠0 = ≠-symmetric $ <→≠ φ

  χ : 0 < (ε / L [ L≠0 ])
  χ = 0</ {ε} {L} ω φ

  ρ : (v : ℝ) →
      Close (L · (ε / L [ L≠0 ])) (0<· {L} {ε / L [ L≠0 ]} φ χ) (f u) (f v) →
      Close ε ω (f u) (f v)
  ρ v σ = σ''
    where
    σ' : Σ (0 < ε) (λ τ → Close ε τ (f u) (f v))
    σ' = subst (λ ?x → Σ (0 < ?x) (λ τ → Close ?x τ _ _))
               (·/ ε L L≠0)
               ((0<· {L} {ε / L [ L≠0 ]} φ χ) , σ)

    σ'' : Close ε ω (f u) (f v)
    σ'' = subst (λ ?x → Close ε ?x _ _) (isProp< 0 ε (fst σ') ω) (snd σ')

continuousAtCompose :
  (f g : ℝ → ℝ)
  (u : ℝ) →
  ContinuousAt f u →
  ContinuousAt g (f u) →
  ContinuousAt (g ∘ f) u
continuousAtCompose f g u φ ψ ε ω =
  ∃-rec
    isPropPropTrunc
    (λ η π →
      ∃-rec
        isPropPropTrunc
        (λ δ ρ → χ η π δ ρ)
        (φ η (fst π)))
    (ψ ε ω)
  where
  χ : (η : ℚ)
      (π : Σ (0 < η)
             (λ ρ → (v : ℝ) → Close η ρ (f u) v → Close ε ω (g (f u)) (g v)))
      (δ : ℚ) →
      Σ (0 < δ) (λ σ → (v : ℝ) → Close δ σ u v → Close η (fst π) (f u) (f v)) →
      ∃ ℚ
        (λ δ →
          Σ (0 < δ)
            (λ υ →
              (v : ℝ) → Close δ υ u v → Close ε ω ((g ∘ f) u) ((g ∘ f) v)))
  χ η (π , ρ) δ (σ , τ) = ∣ δ , σ , χ' ∣₁
    where
    χ' : (v : ℝ) → Close δ σ u v → Close ε ω ((g ∘ f) u) ((g ∘ f) v)
    χ' v = ρ (f v) ∘ τ v

continuousCompose :
  (f g : ℝ → ℝ) →
  Continuous f → Continuous g → Continuous (g ∘ f)
continuousCompose f g φ ψ u = continuousAtCompose f g u (φ u) (ψ $ f u)

lipschitzCompose :
  (g f : ℝ → ℝ)
  (L M : ℚ) (φ : 0 < L) (ψ : 0 < M) →
  Lipschitzℝ g L φ →
  Lipschitzℝ f M ψ →
  Lipschitzℝ (g ∘ f) (L · M) (0<· {x = L} {y = M} φ ψ)
lipschitzCompose g f L M φ ψ ω χ u v ε π ρ = τ'
  where
  σ : Close (L · (M · ε))
              (0<· {x = L} {y = M · ε} φ (0<· {x = M} {y = ε} ψ π))
              (g (f u)) (g (f v))
  σ = (ω (f u) (f v) (M · ε) (0<· {x = M} {y = ε} ψ π)) ((χ u v ε π) ρ)

  τ : Σ (0 < ((L · M) · ε))
        (λ ξ → Close ((L · M) · ε) ξ (g (f u)) (g (f v)))
  τ = subst (λ ?x → Σ (0 < ?x) (λ ξ → Close ?x ξ _ _))
            (·Assoc L M ε)
            (0<· {x = L} {y = M · ε} φ (0<· {x = M} {y = ε} ψ π) , σ)

  τ' : Close ((L · M) · ε)
             (0<· {x = L · M} {y = ε} (0<· {x = L} {y = M} φ ψ) π)
             (g (f u)) (g (f v))
  τ' = subst (λ ?ξ → Close ((L · M) · ε) ?ξ (g (f u)) (g (f v)))
             (isProp< 0 ((L · M) · ε)
               (fst τ)
               (0<· {x = L · M} {y = ε} (0<· {x = L} {y = M} φ ψ) π))
             (snd τ) 

nonexpandingCompose :
  (g f : ℝ → ℝ) →
  Nonexpandingℝ g → Nonexpandingℝ f → Nonexpandingℝ (g ∘ f)
nonexpandingCompose g f φ ψ u v ε ω = (φ (f u) (f v) ε ω) ∘ (ψ u v ε ω)

identityNonexpandingℝ : Nonexpandingℝ $ idfun ℝ
identityNonexpandingℝ u v ε φ ψ = ψ

identityLipschitzℝ : Lipschitzℝ (idfun ℝ) 1 0<1
identityLipschitzℝ = nonexpandingℝ→lipschitzℝ (idfun ℝ) identityNonexpandingℝ

identityContinuous : Continuous $ idfun ℝ
identityContinuous u ε φ = ∣ ε , φ , (λ v → idfun _) ∣₁

constantNonexpandingℝ : (c : ℝ) → Nonexpandingℝ (const c)
constantNonexpandingℝ c u v ε φ ψ = closeReflexive c ε φ

constantLipschitzℝ : (c : ℝ) → Lipschitzℝ (const c) 1 ℚ.0<1
constantLipschitzℝ c =
  nonexpandingℝ→lipschitzℝ (const c) (constantNonexpandingℝ c)

constantContinuous : (u : ℝ) → Continuous $ const u
constantContinuous u v ε φ = ∣ 1 , 0<1 , ψ ∣₁
  where
  ψ : (w : ℝ) → Close 1 0<1 v w → Close ε φ (const u v) (const u w)
  ψ w ω = closeReflexive u ε φ

continuousExtensionLaw₁ :
  (f g : ℝ → ℝ)
  (f' g' : ℚ.ℚ → ℚ.ℚ) →
  (f ∘ rational) ∼ (rational ∘ f') →
  (g ∘ rational) ∼ (rational ∘ g') →
  f' ∼ g' →
  Continuous f →
  Continuous g →
  f ∼ g
continuousExtensionLaw₁ f g f' g' H K L φ ψ =
  continuousExtensionUnique f g φ ψ M
  where
  M : (f ∘ rational) ∼ (g ∘ rational)
  M q = H q ∙ cong rational (L q) ∙ sym (K q)

continuousExtensionLaw₂ :
  (f g : ℝ → ℝ → ℝ)
  (f' g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ) →
  ((q r : ℚ.ℚ) → f (rational q) (rational r) ≡ rational (f' q r)) →
  ((q r : ℚ.ℚ) → g (rational q) (rational r) ≡ rational (g' q r)) →
  ((q r : ℚ.ℚ) → f' q r ≡ g' q r) →
  ((u : ℝ) → Continuous $ f u) →
  ((v : ℝ) → Continuous $ flip f v) →
  ((u : ℝ) → Continuous $ g u) →
  ((v : ℝ) → Continuous $ flip g v) →
  ((u v : ℝ) → f u v ≡ g u v)
continuousExtensionLaw₂ f g f' g' H K L φ ψ ω χ =
  continuousExtensionUnique₂ f g φ ω ψ χ M
  where
  M : (q r : ℚ) →
      f (rational q) (rational r) ≡ g (rational q) (rational r)
  M q r = H q r ∙ cong rational (L q r) ∙ (sym $ K q r)

continuousExtensionLaw₃ :
  (f g : ℝ → ℝ → ℝ → ℝ)
  (f' g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ) →
  ((q r s : ℚ.ℚ) →
    f (rational q) (rational r) (rational s) ≡ rational (f' q r s)) →
  ((q r s : ℚ.ℚ) →
    g (rational q) (rational r) (rational s) ≡ rational (g' q r s)) →
  ((q r s : ℚ.ℚ) → f' q r s ≡ g' q r s) →
  ((u v : ℝ) → Continuous (λ w → f u v w)) →
  ((u w : ℝ) → Continuous (λ v → f u v w)) →
  ((v w : ℝ) → Continuous (λ u → f u v w)) →
  ((u v : ℝ) → Continuous (λ w → g u v w)) →
  ((u w : ℝ) → Continuous (λ v → g u v w)) →
  ((v w : ℝ) → Continuous (λ u → g u v w)) →
  ((u v w : ℝ) → f u v w ≡ g u v w)
continuousExtensionLaw₃ f g f' g' H K L φ ψ ω χ π ρ =
  continuousExtensionUnique₃ f g φ ψ ω χ π ρ M
  where
  M : (q r s : ℚ) →
      f (rational q) (rational r) (rational s) ≡
      g (rational q) (rational r) (rational s)
  M q r s = H q r s ∙ cong rational (L q r s) ∙ (sym $ K q r s)

rationalInjective : {q r : ℚ} → rational q ≡ rational r → q ≡ r
rationalInjective {q} {r} p = ω
  where
  φ : (ε : ℚ) (ω : 0 < ε) → Close ε ω (rational q) (rational r)
  φ ε ω = subst (Close ε ω (rational q))
                p
                (closeReflexive (rational q) ε ω)

  ψ : (ε : ℚ) (ω : 0 < ε) → ∣ q - r ∣ < ε
  ψ ε ω = close→close' (rational q) (rational r) ε ω (φ ε ω)

  ω : q ≡ r
  ω = distance<ε→≡ ψ

rationalEmbedding : isEmbedding rational 
rationalEmbedding = injEmbedding ℝ-isSet rationalInjective

eventuallyConstantAt≡constant :
  (θ : ℚ) (φ : 0 < θ)
  (x : (ε : ℚ) → 0 < ε → ℝ)
  (ψ : CauchyApproximation x)
  (c : ℝ) →
  EventuallyConstantAt θ φ x c →
  limit x ψ ≡ c
eventuallyConstantAt≡constant θ φ x ψ c ω =
  path (limit x ψ) c χ
  where
  χ : (ε : ℚ) (π : 0 < ε) → Close ε π (limit x ψ) c
  χ ε π = limitClose' c x ψ ε δ π τ σ' ξ
    where
    δ : ℚ
    δ = min (θ / 2 [ 2≠0 ]) (ε / 2 [ 2≠0 ])

    ρ : δ < θ
    ρ = isTrans≤< δ (θ / 2 [ 2≠0 ]) θ
                  (min≤ (θ / 2 [ 2≠0 ]) (ε / 2 [ 2≠0 ]))
                  (self/2<self θ φ)

    σ : δ < ε
    σ = isTrans≤< δ (ε / 2 [ 2≠0 ]) ε
                  (min≤' (θ / 2 [ 2≠0 ]) (ε / 2 [ 2≠0 ]))
                  (self/2<self ε π)

    σ' : 0 < ε - δ
    σ' = <→0<- {x = δ} {y = ε} σ

    τ : 0 < δ
    τ = minGreatestLowerBound<
          {x = θ / 2 [ 2≠0 ]} {y = ε / 2 [ 2≠0 ]} {z = 0}
          (0</ {x = θ} {y = 2} φ 0<2)
          (0</ {x = ε} {y = 2} π 0<2)

    υ : x δ τ ≡ c
    υ = ω δ τ ρ

    ξ : x δ τ ∼[ ε - δ , σ' ] c
    ξ = subst (λ ?x → x δ τ ∼[ ε - δ , σ' ] ?x)
              υ
              (closeReflexive (x δ τ) (ε - δ) σ')

lipschitz₂-composeLipschitz₁-lipschitz :
  {f g : ℝ → ℝ} {h : ℝ → ℝ → ℝ} →
  (L M N₁ N₂ : ℚ) (φ : 0 < L) (ψ : 0 < M) (ω : 0 < N₁) (χ : 0 < N₂) →
  Lipschitzℝ f L φ →
  Lipschitzℝ g M ψ →
  ((y : ℝ) → Lipschitzℝ (flip h y) N₁ ω) →
  ((x : ℝ) → Lipschitzℝ (h x) N₂ χ) →
  let
    ξ : 0 < N₁ · L + N₂ · M
    ξ = (0<+' {x = N₁ · L} {y = N₂ · M}
          (0<· {x = N₁} {y = L} ω φ) (0<· {x = N₂} {y = M} χ ψ))
  in Lipschitzℝ (λ x → h (f x) (g x)) (N₁ · L + N₂ · M) ξ
lipschitz₂-composeLipschitz₁-lipschitz {f} {g} {h}
  L M N₁ N₂ φ ψ ω χ π ρ σ τ x y ε υ ο =
  μ'
  where
  ξ : 0 < N₁ · L + N₂ · M
  ξ = (0<+' {x = N₁ · L} {y = N₂ · M}
      (0<· {x = N₁} {y = L} ω φ) (0<· {x = N₂} {y = M} χ ψ))

  α' : 0 < L · ε
  α' = 0<· {x = L} {y = ε} φ υ

  α : f x ∼[ L · ε , α' ] f y
  α = π x y ε υ ο

  β' : 0 < M · ε 
  β' = 0<· {x = M} {y = ε} ψ υ

  β : g x ∼[ M · ε , β' ] g y
  β = ρ x y ε υ ο

  γ' : 0 < N₁ · (L · ε) 
  γ' = 0<· {x = N₁} {y = L · ε} ω α'

  γ : h (f x) (g x) ∼[ N₁ · (L · ε) , γ' ] h (f y) (g x)
  γ = σ (g x) (f x) (f y) (L · ε) α' α

  ζ' : 0 < N₂ · (M · ε)
  ζ' = 0<· {x = N₂} {y = M · ε} χ β'

  ζ : h (f y) (g x) ∼[ N₂ · (M · ε) , ζ' ] h (f y) (g y)
  ζ = τ (f y) (g x) (g y) (M · ε) β' β

  ι' : 0 < N₁ · (L · ε) + N₂ · (M · ε)
  ι' = 0<+' {x = N₁ · (L · ε)} {y = N₂ · (M · ε)} γ' ζ'

  ι : h (f x) (g x) ∼[ N₁ · (L · ε) + N₂ · (M · ε) , ι' ] h (f y) (g y)
  ι = closeTriangleInequality
        (h (f x) (g x)) (h (f y) (g x)) (h (f y) (g y))
        (N₁ · (L · ε)) (N₂ · (M · ε)) γ' ζ'
        γ ζ
  
  κ : N₁ · (L · ε) + N₂ · (M · ε) ≡ (N₁ · L + N₂ · M) · ε
  κ = N₁ · (L · ε) + N₂ · (M · ε)
        ≡⟨ cong (flip _+_ (N₂ · (M · ε))) (·Assoc N₁ L ε)  ⟩
      (N₁ · L) · ε + N₂ · (M · ε)
        ≡⟨ cong (_+_ ((N₁ · L) · ε)) (·Assoc N₂ M ε) ⟩
      (N₁ · L) · ε + (N₂ · M) · ε
        ≡⟨ (sym $ ·DistR+ (N₁ · L) (N₂ · M) ε) ⟩
      (N₁ · L + N₂ · M) · ε ∎

  μ : Σ (0 < (N₁ · L + N₂ · M) · ε)
        (λ ξ' → h (f x) (g x) ∼[ (N₁ · L + N₂ · M) · ε , ξ' ] h (f y) (g y))
  μ = subst (λ ?x → Σ (0 < ?x)
                      (λ ξ' → h (f x) (g x) ∼[ ?x , ξ' ] h (f y) (g y)))
            κ
            (ι' , ι)

  ξ' : 0 < (N₁ · L + N₂ · M) · ε
  ξ' = 0<· {x = N₁ · L + N₂ · M} {y = ε} ξ υ

  μ' : h (f x) (g x) ∼[ (N₁ · L + N₂ · M) · ε , ξ' ] h (f y) (g y)
  μ' = subst
         (λ ?ξ → h (f x) (g x) ∼[ (N₁ · L + N₂ · M) · ε , ?ξ ] h (f y) (g y))
         (isProp< 0 ((N₁ · L + N₂ · M) · ε) (fst μ) ξ')
         (snd μ)

-- TODO: Think this will only actually work if the h function is uniformly continuous
-- continuous₂-composeContinuous₁-continuous :
--   {f g : ℝ → ℝ} {h : ℝ → ℝ → ℝ} →
--   Continuous f →
--   Continuous g →
--   ((y : ℝ) → Continuous $ flip h y) →
--   ((x : ℝ) → Continuous $ h x) →
--   Continuous (λ x → h (f x) (g x))
-- continuous₂-composeContinuous₁-continuous {f} {g} {h} φ ψ ω χ x ε π = {!!}
--   where
--   ρ : 0 < ε / 2 [ ℚ.2≠0 ]
--   ρ = ℚ.0</ {x = ε} {y = 2} π ℚ.0<2

--   σ : ∃ ℚ
--       (λ δ₁ →
--       Σ (0 ℚ.< δ₁)
--       (λ ξ → (v : ℝ) →
--       Close δ₁ ξ (f x) v →
--       Close (ε / 2 [ ℚ.2≠0 ]) ρ (h (f x) (g x)) (h v (g x))))
--   σ = ω (g x) (f x) (ε / 2 [ ℚ.2≠0 ]) ρ

--   τ : ∃ ℚ
--       (λ δ₂ → Σ (0 ℚ.< δ₂)
--       (λ ξ → (v : ℝ) →
--       Close δ₂ ξ (g x) v →
--       Close (ε / 2 [ ℚ.2≠0 ]) ρ (h (f y) (g x)) (h v (g x))))
--   τ = ψ (f y) x (ε / 2 [ ℚ.2≠0 ]) ρ

--   υ : ∃ ℚ
--       (λ δ →
--       Σ (0 ℚ.< δ)
--       (λ ξ → (y : ℝ) →
--       Close δ ξ x y →
--       Close (ε / 2 [ ℚ.2≠0 ]) ρ (h (f x) (g x)) (h (f y) (g y))))
--   υ = PropositionalTruncation.map2 υ' σ τ
--     where
--     υ' : Σ ℚ
--          (λ δ₁ →
--          Σ (0 ℚ.< δ₁)
--          (λ ξ → (v : ℝ) →
--          Close δ₁ ξ (f x) v →
--          Close (ε / 2 [ ℚ.2≠0 ]) ρ (h (f x) (g x)) (h v (g x)))) →
--          Σ ℚ
--          (λ δ₂ →
--          Σ (0 < δ₂)
--          (λ ξ →
--          (y : ℝ) → Close δ₂ ξ x y →
--                    Close (ε / 2 [ 2≠0 ]) ρ (g x) (g y))) →
--          Σ ℚ
--          (λ δ →
--          Σ (0 < δ)
--          (λ ξ →
--          (y : ℝ) →
--          Close δ ξ x y →
--          Close (ε / 2 [ 2≠0 ]) ρ (h (f x) (g x)) (h (f y) (g y))))
--     υ' (δ₁ , (α₁ , β₁)) (δ₂ , (α₂ , β₂)) = {!!}
--       where
--       δ : ℚ.ℚ
--       δ = ℚ.min δ₁ δ₂

--       α : 0 ℚ.< δ
--       α = minGreatestLowerBound< {x = δ₁} {y = δ₂} {z = 0} α₁ α₂
      
--       γ₁ : ∃ ℚ (λ η₁ →
--            Σ (0 ℚ.< η₁)
--            (λ ξ → (y : ℝ) → Close η₁ ξ x y →
--                             Close δ α (f x) (f y)))
--       γ₁ = {!ψ !}

--       γ₂ : ∃ ℚ (λ η₂ →
--            Σ (0 ℚ.< η₂)
--            (λ ξ → (y : ℝ) → Close η₂ ξ x y →
--                             Close δ α (g x) (g y)))
--       γ₂ = {!!}
