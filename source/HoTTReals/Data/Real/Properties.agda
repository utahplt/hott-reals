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
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction

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

nonexpanding₂→lipschitz₂ : 
  (f : ℝ → ℝ → ℝ) →
  (φ : Nonexpandingℝ₂ f) →
  (u : ℝ) → Lipschitzℝ (f u) 1 0<1 
nonexpanding₂→lipschitz₂ f φ u v w ε ψ ω =
  ρ
  where
  χ : Close ε ψ (f u v) (f u w)
  χ = snd φ u v w ε ψ ω

  π : Σ (0 < 1 · ε) (λ ρ → Close (1 · ε) ρ (f u v) (f u w))
  π = subst (λ ?x → Σ (0 < ?x) (λ ρ → Close ?x ρ _ _)) (sym $ ·IdL ε) (ψ , χ)

  ρ : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ) (f u v) (f u w)
  ρ = subst (λ ?x → Close (1 · ε) ?x (f u v) (f u w))
            (isProp< 0 (1 · ε) (fst π) (0<· {x = 1} {y = ε} 0<1 ψ))
            (snd π)

nonexpanding₂→lipschitz₁ : 
  (f : ℝ → ℝ → ℝ) →
  (φ : Nonexpandingℝ₂ f) →
  (w : ℝ) → Lipschitzℝ (flip f w) 1 0<1 
nonexpanding₂→lipschitz₁ f φ w u v ε ψ ω =
  ρ
  where
  χ : Close ε ψ (f u w) (f v w)
  χ = fst φ u v w ε ψ ω

  π : Σ (0 < 1 · ε) (λ ρ → Close (1 · ε) ρ (f u w) (f v w))
  π = subst (λ ?x → Σ (0 < ?x) (λ ρ → Close ?x ρ _ _)) (sym $ ·IdL ε) (ψ , χ)

  ρ : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ) (f u w) (f v w)
  ρ = subst (λ ?x → Close (1 · ε) ?x (f u w) (f v w))
            (isProp< 0 (1 · ε) (fst π) (0<· {x = 1} {y = ε} 0<1 ψ))
            (snd π)

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

identityContinuous : Continuous $ idfun ℝ
identityContinuous u ε φ = ∣ ε , φ , (λ v → idfun _) ∣₁

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
