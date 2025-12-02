module HoTTReals.Data.Real.Lipschitz where

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

liftLipschitzRecursion :
  (f : ℚ → ℝ)
  (L : ℚ) (φ : 0 < L) →
  Lipschitzℚ f L φ →
  Recursion ℝ (λ u v ε ω → u ∼[ L · ε , 0<· {x = L} {y = ε} φ ω ] v)
liftLipschitzRecursion f L φ ψ =
  liftLipschitzRational ,
  liftLipschitzLimit ,
  bSeperated ,
  rationalRationalCase ,
  rationalLimitCase ,
  limitRationalCase ,
  limitLimitCase ,
  bProposition
  where
  B : (u v : ℝ) (ε : ℚ) (φ : 0 < ε) → Type ℓ-zero
  B = λ u v ε ω → u ∼[ L · ε , 0<· {x = L} {y = ε} φ ω ] v

  L≠0 : ¬ L ≡ 0
  L≠0 = ≠-symmetric $ <→≠ φ

  liftLipschitzRational : ℚ → ℝ
  liftLipschitzRational = f

  liftLipschitzApproximation : ((ε : ℚ) → 0 < ε → ℝ) → ((ε : ℚ) → 0 < ε → ℝ)
  liftLipschitzApproximation f ε χ = f (ε / L [ L≠0 ]) (0</ {x = ε} {y = L} χ φ)

  liftLipschitzApproximationCauchy :
    (f : (ε : ℚ) → 0 < ε → ℝ) →
    CauchyApproximation'' ℝ B f →
    CauchyApproximation (liftLipschitzApproximation f)
  liftLipschitzApproximationCauchy f ω ε δ π ρ = υ'
    where
    σ = ω (ε / L [ L≠0 ]) (δ / L [ L≠0 ])
          (0</ {x = ε} {y = L} π φ) (0</ {x = δ} {y = L} ρ φ)

    τ : L · ((ε / L [ L≠0 ]) + (δ / L [ L≠0 ])) ≡ ε + δ
    τ = L · ((ε / L [ L≠0 ]) + (δ / L [ L≠0 ]))
             ≡⟨ cong (_·_ L) (sym $ ·DistR+ ε δ (L [ L≠0 ]⁻¹)) ⟩
           L · ((ε + δ) · L [ L≠0 ]⁻¹)
             ≡⟨ cong (_·_ L) (·Comm (ε + δ) (L [ L≠0 ]⁻¹)) ⟩
           L · (L [ L≠0 ]⁻¹ · (ε + δ))
             ≡⟨ ·Assoc L (L [ L≠0 ]⁻¹) (ε + δ) ⟩
           (L · L [ L≠0 ]⁻¹) · (ε + δ)
              ≡⟨ cong (flip _·_ (ε + δ)) (⁻¹-inverse L L≠0) ⟩
           1 · (ε + δ)
             ≡⟨ ·IdL (ε + δ) ⟩
           ε + δ ∎

    υ : Σ (0 < ε + δ)
          (λ ξ → Close (ε + δ) ξ
                       (f (ε / L [ L≠0 ]) (0</ {x = ε} {y = L} π φ))
                       (f (δ / L [ L≠0 ]) (0</ {x = δ} {y = L} ρ φ)))
    υ = subst (λ ?x → Σ (0 < ?x) (λ ξ → Close ?x ξ _ _))
        τ
        ((0<· {x = L} {y = (ε / L [ L≠0 ]) + (δ / L [ L≠0 ])}
           φ (0<+' {x = ε / L [ L≠0 ]} {y = δ / L [ L≠0 ]}
               (0</ {x = ε} {y = L} π φ)
               (0</ {x = δ} {y = L} ρ φ))) , σ)


    υ' : Close (ε + δ) (0<+' {x = ε} {y = δ} π ρ)
               (f (ε / L [ L≠0 ]) (0</ {x = ε} {y = L} π φ))
               (f (δ / L [ L≠0 ]) (0</ {x = δ} {y = L} ρ φ))
    υ' = subst (λ ?x → Close (ε + δ) ?x _ _)
               (isProp< 0 (ε + δ) (fst υ) (0<+' {x = ε} {y = δ} π ρ))
               (snd υ)

  liftLipschitzLimit :
    (x : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation x)
    (f : (ε : ℚ) → 0 < ε → ℝ) →
    CauchyApproximation'' ℝ B f →
    ℝ
  liftLipschitzLimit _ _ f ω =
    limit (liftLipschitzApproximation f)
          (liftLipschitzApproximationCauchy f ω)

  bSeperated :
    (u v : ℝ) →
    ((ε : ℚ) (ω : 0 < ε) → Close (L · ε) (0<· {x = L} {y = ε} φ ω) u v) → u ≡ v
  bSeperated u v ω = path u v χ
    where
    χ : (ε : ℚ) (π : 0 < ε) → Close ε π u v
    χ ε π = σ'
      where
      ρ : Close (L · (ε / L [ L≠0 ]))
                (0<· {x = L} {y = ε / L [ L≠0 ]} φ
                  (0</ {x = ε} {y = L} π φ))
                u v
      ρ = ω (ε / L [ L≠0 ]) (0</ {x = ε} {y = L} π φ)

      σ : Σ (0 < ε) (λ τ → Close ε τ u v)
      σ = subst (λ ?x → Σ (0 < ?x) (λ τ → Close ?x τ u v))
                (·/ ε L L≠0)
                (((0<· {x = L} {y = ε / L [ L≠0 ]} φ
                    (0</ {x = ε} {y = L} π φ))) ,
                 ρ)

      σ' : Close ε π u v
      σ' = subst (λ ?x → Close ε ?x u v)
           (isProp< 0 ε (fst σ) π)
           (snd σ)

  rationalRationalCase :
    (q r ε : ℚ) (ω : 0 < ε) →
    - ε < q - r → q - r < ε →
    Close (L · ε) (0<· {x = L} {y = ε} φ ω)
          (liftLipschitzRational q)
          (liftLipschitzRational r)
  rationalRationalCase q r ε ω χ π = ψ q r ε ω (<→∣∣< {x = q - r} {ε = ε} π χ)

  rationalLimitCase :
    (q ε δ : ℚ) (ω : 0 < ε) (χ : 0 < δ) (π : 0 < (ε - δ))
    (y : (ε₁ : ℚ) → 0 < ε₁ → ℝ) (ρ : CauchyApproximation y)
    (g : (ε₁ : ℚ) → 0 < ε₁ → ℝ) (σ : CauchyApproximation'' ℝ B g) →
    Close (ε - δ) π (rational q) (y δ χ) →
    Close (L · (ε - δ)) (0<· {x = L} {y = ε - δ} φ π)
      (liftLipschitzRational q) (g δ χ) →
    Close (L · ε) (0<· {x = L} {y = ε} φ ω)
      (liftLipschitzRational q)
      (liftLipschitzLimit y ρ g σ)
  rationalLimitCase q ε δ ω χ π y ρ g σ τ υ =
    closeLimit' (liftLipschitzRational q)
                (liftLipschitzApproximation g)
                (liftLipschitzApproximationCauchy g σ)
                (L · ε) (L · δ)
                (0<· {x = L} {y = ε} φ ω) (0<· {x = L} {y = δ} φ χ)
                (fst ο) ο'
    where
    -- TODO: Pull into lemma
    ξ : L · (ε - δ) ≡ (L · ε) - (L · δ)
    ξ = L · (ε - δ)
         ≡⟨ ·DistL+ L ε (- δ) ⟩
        (L · ε) + (L · (- δ))
         ≡⟨ cong (_+_ (L · ε)) (sym $ -·≡·- L δ) ⟩
        (L · ε) - (L · δ) ∎

    ο : Σ (0 < (L · ε) - (L · δ))
          (λ α → Close ((L · ε) - (L · δ)) α (liftLipschitzRational q) (g δ χ))
    ο = subst (λ ?x → Σ (0 < ?x) (λ α → Close ?x α _ _))
              ξ
              ((0<· {x = L} {y = ε - δ} φ π) , υ)

    α : g δ χ ≡ (liftLipschitzApproximation g (L · δ) (0<· {x = L} {y = δ} φ χ))
    α = cong₂ g
              (sym $ ·/' L δ L≠0)
              (isProp→PathP
                (λ i → isProp< 0 (·/' L δ L≠0 (~ i)))
                χ
                (0</ {x = L · δ} {y = L} (0<· {x = L} {y = δ} φ χ) φ))

    ο' : Close ((L · ε) - (L · δ)) (fst ο)
               (liftLipschitzRational q)
               (liftLipschitzApproximation g (L · δ) (0<· {x = L} {y = δ} φ χ))
    ο' = subst (Close _ _ _) α (snd ο)

  limitRationalCase :
    (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y)
    (g : (ε : ℚ) → 0 < ε → ℝ)
    (χ : CauchyApproximation'' ℝ B g)
    (r ε δ : ℚ) (π : 0 < ε) (ρ : 0 < δ) (σ : 0 < (ε - δ)) →
    Close (ε - δ) σ (y δ ρ) (rational r) →
    Close (L · (ε - δ)) (0<· {x = L} {y = ε - δ} φ σ)
          (g δ ρ) (liftLipschitzRational r) →
    Close (L · ε) (0<· {x = L} {y = ε} φ π)
          (liftLipschitzLimit y ω g χ)
          (liftLipschitzRational r)
  limitRationalCase y ω g χ r ε δ π ρ σ τ υ =
    closeSymmetric
      (liftLipschitzRational r)
      (liftLipschitzLimit y ω g χ)
      (L · ε)
      (0<· {x = L} {y = ε} φ π)
      (closeLimit'
        (liftLipschitzRational r)
        (liftLipschitzApproximation g) (liftLipschitzApproximationCauchy g χ)
        (L · ε) (L · δ)
        (0<· {x = L} {y = ε} φ π) (0<· {x = L} {y = δ} φ ρ) (fst ο)
        (closeSymmetric
          (liftLipschitzApproximation g (L · δ)
            (0<· {x = L} {y = δ} φ ρ))
          (liftLipschitzRational r)
          ((L · ε) - (L · δ))
          (fst ο) ο'))
    where
    ξ : L · (ε - δ) ≡ (L · ε) - (L · δ)
    ξ = L · (ε - δ)
          ≡⟨ ·DistL+ L ε (- δ) ⟩
        (L · ε) + (L · (- δ))
          ≡⟨ cong (_+_ (L · ε)) (sym $ -·≡·- L δ ) ⟩
        (L · ε) - (L · δ) ∎

    ο : Σ (0 < (L · ε) - (L · δ))
          (λ α → Close ((L · ε) - (L · δ)) α (g δ ρ) (liftLipschitzRational r))
    ο = subst (λ ?x → Σ (0 < ?x) (λ α → Close ?x α _ _))
              ξ
              ((0<· {x = L} {y = ε - δ} φ σ) , υ)

    α : g δ ρ ≡ (liftLipschitzApproximation g (L · δ) (0<· {x = L} {y = δ} φ ρ))
    α = cong₂ g
              (sym $ ·/' L δ L≠0)
              (isProp→PathP
                (λ i → isProp< 0 (·/' L δ L≠0 (~ i)))
                ρ
                (0</ {x = L · δ} {y = L} (0<· {x = L} {y = δ} φ ρ) φ))

    ο' : Close ((L · ε) - (L · δ)) (fst ο)
               (liftLipschitzApproximation g (L · δ) (0<· {x = L} {y = δ} φ ρ))
               (liftLipschitzRational r)
    ο' = subst (λ ?x → Close _ (fst ο) ?x _) α (snd ο)

  limitLimitCase :
    (x y f g : (ε : ℚ) → 0 < ε → ℝ)
    (ω : CauchyApproximation x) (χ : CauchyApproximation y)
    (π : CauchyApproximation'' ℝ B f) (ρ : CauchyApproximation'' ℝ B g)
    (ε δ η : ℚ) (σ : 0 < ε) (τ : 0 < δ) (υ : 0 < η) (ξ : 0 < ε - (δ + η)) →
    Close (ε - (δ + η)) ξ (x δ τ) (y η υ) →
    Close (L · (ε - (δ + η)))
          (0<· {x = L} {y = ε - (δ + η)} φ ξ)
          (f δ τ) (g η υ) →
    Close (L · ε)
          (0<· {x = L} {y = ε} φ σ)
          (liftLipschitzLimit x ω f π) (liftLipschitzLimit y χ g ρ)
  limitLimitCase x y f g ω χ π ρ ε δ η σ τ υ ξ ο α =
    limitLimit
      (liftLipschitzApproximation f) (liftLipschitzApproximation g)
      (liftLipschitzApproximationCauchy f π)
      (liftLipschitzApproximationCauchy g ρ)
      (L · ε) (L · δ) (L · η)
      (0<· {x = L} {y = ε} φ σ)
      (0<· {x = L} {y = δ} φ τ)
      (0<· {x = L} {y = η} φ υ)
      (fst γ) κ
    where
      β : L · (ε - (δ + η)) ≡ (L · ε) - ((L · δ) + (L · η))
      β = L · (ε - (δ + η))
            ≡⟨ ·DistL+ L ε (- (δ + η)) ⟩
          (L · ε) + (L · - (δ + η))
            ≡⟨ cong (_+_ (L · ε)) (sym $ -·≡·- L (δ + η)) ⟩
          (L · ε) + - (L · (δ + η))
            ≡⟨ cong (λ ?x → (L · ε) + - ?x) (·DistL+ L δ η) ⟩
          (L · ε) + - ((L · δ) + (L · η)) ∎

      γ : Σ (0 < (L · ε) - ((L · δ) + (L · η)))
                 (λ ζ → Close ((L · ε) - ((L · δ) + (L · η))) ζ (f δ τ) (g η υ))
      γ = subst (λ ?x → Σ (0 < ?x) (λ ζ → Close ?x ζ _ _))
                β
                (0<· {x = L} {y = ε - (δ + η)} φ ξ , α)

      ζ : f δ τ ≡ liftLipschitzApproximation f (L · δ) (0<· {x = L} {y = δ} φ τ)
      ζ = cong₂ f
                (sym $ ·/' L δ L≠0)
                (isProp→PathP
                  -- TODO: What on earth is going on here?
                  (λ i → isProp< 0 (·/' L δ L≠0 (~ i)))
                  τ
                  (0</ {x = L · δ} {y = L} (0<· {x = L} {y = δ} φ τ) φ))

      ι : g η υ ≡ liftLipschitzApproximation g (L · η) (0<· {x = L} {y = η} φ υ)
      ι = cong₂ g
                (sym $ ·/' L η L≠0)
                (isProp→PathP
                  (λ i → isProp< 0 (·/' L η L≠0 (~ i)))
                  υ
                  (0</ {x = L · η} {y = L} (0<· {x = L} {y = η} φ υ) φ))

      κ : Close ((L · ε) - ((L · δ) + (L · η))) (fst γ)
                (liftLipschitzApproximation f (L · δ)
                  (0<· {x = L} {y = δ} φ τ))
                (liftLipschitzApproximation g (L · η)
                  (0<· {x = L} {y = η} φ υ))
      κ = subst2 (Close _ _) ζ ι (snd γ)

  bProposition :
    (u v : ℝ) (ε : ℚ) (ω : 0 < ε) →
    isProp (Close (L · ε) (0<· {x = L} {y = ε} φ ω) u v)
  bProposition u v ε ω = squash (L · ε) (0<· {x = L} {y = ε} φ ω) u v

liftLipschitz :
  (f : ℚ → ℝ)
  (L : ℚ) (φ : 0 < L) →
  Lipschitzℚ f L φ →
  (ℝ → ℝ)
liftLipschitz f L φ ψ = recursion (liftLipschitzRecursion f L φ ψ)

liftLipschitzLipschitz :
  (f : ℚ → ℝ)
  (L : ℚ) (φ : 0 < L)
  (ψ : Lipschitzℚ f L φ) →
  Lipschitzℝ (liftLipschitz f L φ ψ) L φ
liftLipschitzLipschitz f L φ ψ =
  λ u v ε ω → recursion∼ (liftLipschitzRecursion f L φ ψ)

liftLipschitz≡rational :
  (f : ℚ → ℝ)
  (L : ℚ) (φ : 0 < L)
  (ψ : Lipschitzℚ f L φ)
  (q : ℚ) →
  liftLipschitz f L φ ψ (rational q) ≡ f q
liftLipschitz≡rational f L φ ψ q = refl
