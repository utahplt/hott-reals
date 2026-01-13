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

liftLipschitzApproximation :
  (f : (ε : ℚ) → 0 < ε → ℝ)
  (L : ℚ) (φ : 0 < L) →
  ((ε : ℚ) → 0 < ε → ℝ)
liftLipschitzApproximation f L φ ε ψ =
  let
    φ' : ¬ L ≡ 0
    φ' = ≠-symmetric $ <→≠ φ

    ω : 0 < ε / L [ φ' ]
    ω = 0</ {x = ε} {y = L} ψ φ
  in f (ε / L [ φ' ]) ω

LiftLipschitzRelation :
  (L : ℚ) (φ : 0 < L)
  (u v : ℝ) (ε : ℚ) (ψ : 0 < ε) → Type ℓ-zero
LiftLipschitzRelation L φ u v ε ψ = u ∼[ L · ε , 0<· {x = L} {y = ε} φ ψ ] v

liftLipschitzRelationProposition :
  (L : ℚ) (φ : 0 < L)
  (u v : ℝ) (ε : ℚ) (ψ : 0 < ε) →
  isProp $ LiftLipschitzRelation L φ u v ε ψ
liftLipschitzRelationProposition L φ u v ε ψ =
  squash (L · ε) (0<· {x = L} {y = ε} φ ψ) u v

liftLipschitzRelationSeparated :
  (L : ℚ) (φ : 0 < L)
  (u v : ℝ) →
  ((ε : ℚ) (ψ : 0 < ε) → Close (L · ε) (0<· {x = L} {y = ε} φ ψ) u v) →
  u ≡ v
liftLipschitzRelationSeparated L φ u v ψ = path u v ω
  where
  ω : (ε : ℚ) (χ : 0 < ε) → Close ε χ u v
  ω ε χ = σ
    where
    φ' : ¬ L ≡ 0 
    φ' = ≠-symmetric $ <→≠ φ

    π : Close (L · (ε / L [ φ' ]))
              (0<· {x = L} {y = ε / L [ φ' ]} φ (0</ {x = ε} {y = L} χ φ))
              u v
    π = ψ (ε / L [ φ' ]) (0</ {x = ε} {y = L} χ φ)

    ρ : Σ (0 < ε) (λ σ → Close ε σ u v)
    ρ = subst (λ ?x → Σ (0 < ?x) (λ τ → Close ?x τ u v))
              (·/ ε L φ')
              ((0<· {x = L} {y = ε / L [ φ' ]} φ (0</ {x = ε} {y = L} χ φ)) ,
               π)

    σ : Close ε χ u v
    σ = subst (λ ?x → Close ε ?x u v) (isProp< 0 ε (fst ρ) χ) (snd ρ)

liftLipschitzApproximationCauchy :
  (f : (ε : ℚ) → 0 < ε → ℝ) →
  (L : ℚ) (φ : 0 < L) →
  CauchyApproximation'' ℝ (LiftLipschitzRelation L φ) f →
  CauchyApproximation (liftLipschitzApproximation f L φ)
liftLipschitzApproximationCauchy f L φ ψ ε δ ω χ =
  σ'
  where
  φ' : ¬ L ≡ 0 
  φ' = ≠-symmetric $ <→≠ φ

  π : LiftLipschitzRelation L φ
        (f (ε / L [ φ' ]) (0</ {x = ε} {y = L} ω φ))
        (f (δ / L [ φ' ]) (0</ {x = δ} {y = L} χ φ))
        ((ε / L [ φ' ]) + (δ / L [ φ' ]))
        (0<+' {x = ε / L [ φ' ]} {y = δ / L [ φ' ]}
          (0</ {x = ε} {y = L} ω φ) (0</ {x = δ} {y = L} χ φ))
  π = ψ (ε / L [ φ' ]) (δ / L [ φ' ])
        (0</ {x = ε} {y = L} ω φ) (0</ {x = δ} {y = L} χ φ)

  ρ : L · ((ε / L [ φ' ]) + (δ / L [ φ' ])) ≡ ε + δ
  ρ = L · ((ε / L [ φ' ]) + (δ / L [ φ' ]))
        ≡⟨ cong (_·_ L) (sym $ ·DistR+ ε δ (L [ φ' ]⁻¹)) ⟩
      L · ((ε + δ) · L [ φ' ]⁻¹)
        ≡⟨ cong (_·_ L) (·Comm (ε + δ) (L [ φ' ]⁻¹)) ⟩
      L · (L [ φ' ]⁻¹ · (ε + δ))
        ≡⟨ ·Assoc L (L [ φ' ]⁻¹) (ε + δ) ⟩
      (L · L [ φ' ]⁻¹) · (ε + δ)
        ≡⟨ cong (flip _·_ (ε + δ)) (⁻¹-inverse L φ') ⟩
      1 · (ε + δ)
        ≡⟨ ·IdL (ε + δ) ⟩
      ε + δ ∎

  σ : Σ (0 < ε + δ)
        (λ ξ → Close (ε + δ) ξ
                     (f (ε / L [ φ' ]) (0</ {x = ε} {y = L} ω φ))
                     (f (δ / L [ φ' ]) (0</ {x = δ} {y = L} χ φ)))
  σ = subst (λ ?x → Σ (0 < ?x)
              (λ ξ → Close ?x ξ (f (ε / L [ φ' ]) (0</ {x = ε} {y = L} ω φ))
                                (f (δ / L [ φ' ]) (0</ {x = δ} {y = L} χ φ))))
            ρ
            (0<· {x = L} {y = (ε / L [ φ' ]) + (δ / L [ φ' ])}
              φ (0<+' {x = ε / L [ φ' ]} {y = δ / L [ φ' ]}
                  (0</ {x = ε} {y = L} ω φ) (0</ {x = δ} {y = L} χ φ)) ,
             π)

  σ' : Close (ε + δ) (0<+' {x = ε} {y = δ} ω χ)
             (f (ε / L [ φ' ]) (0</ {x = ε} {y = L} ω φ))
             (f (δ / L [ φ' ]) (0</ {x = δ} {y = L} χ φ))
  σ' = subst (λ ?x → Close (ε + δ) ?x
                (f (ε / L [ φ' ]) (0</ {x = ε} {y = L} ω φ))
                (f (δ / L [ φ' ]) (0</ {x = δ} {y = L} χ φ)))
             (isProp< 0 (ε + δ) (fst σ) (0<+' {x = ε} {y = δ} ω χ))
             (snd σ)

liftLipschitzRecursion :
  (f : ℚ → ℝ)
  (L : ℚ) (φ : 0 < L) →
  Lipschitzℚ f L φ →
  Recursion ℝ (λ u v ε ω → u ∼[ L · ε , 0<· {x = L} {y = ε} φ ω ] v)
liftLipschitzRecursion f L φ ψ =
  liftLipschitzRational ,
  liftLipschitzLimit ,
  liftLipschitzRelationSeparated L φ ,
  rationalRationalCase ,
  rationalLimitCase ,
  limitRationalCase ,
  limitLimitCase ,
  (liftLipschitzRelationProposition L φ)
  where
  φ' : ¬ L ≡ 0
  φ' = ≠-symmetric $ <→≠ φ

  liftLipschitzRational : ℚ → ℝ
  liftLipschitzRational = f

  liftLipschitzLimit :
    (x : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation x)
    (f : (ε : ℚ) → 0 < ε → ℝ) →
    CauchyApproximation'' ℝ (LiftLipschitzRelation L φ) f →
    ℝ
  liftLipschitzLimit _ _ f ω =
    limit (liftLipschitzApproximation f L φ)
          (liftLipschitzApproximationCauchy f L φ ω)

  rationalRationalCase :
    (q r ε : ℚ) (ω : 0 < ε) →
    - ε < q - r → q - r < ε →
    Close (L · ε) (0<· {x = L} {y = ε} φ ω)
          (liftLipschitzRational q)
          (liftLipschitzRational r)
  rationalRationalCase q r ε ω χ π = ψ q r ε ω (<→∣∣< {x = q - r} {ε = ε} π χ)

  rationalLimitCase :
    (q ε δ : ℚ) (ω : 0 < ε) (χ : 0 < δ) (π : 0 < (ε - δ))
    (y : (ε₁ : ℚ) → 0 < ε₁ → ℝ)
    (ρ : CauchyApproximation y)
    (g : (ε₁ : ℚ) → 0 < ε₁ → ℝ)
    (σ : CauchyApproximation'' ℝ (LiftLipschitzRelation L φ) g) →
    Close (ε - δ) π (rational q) (y δ χ) →
    Close (L · (ε - δ)) (0<· {x = L} {y = ε - δ} φ π)
      (liftLipschitzRational q) (g δ χ) →
    Close (L · ε) (0<· {x = L} {y = ε} φ ω)
      (liftLipschitzRational q)
      (liftLipschitzLimit y ρ g σ)
  rationalLimitCase q ε δ ω χ π y ρ g σ τ υ =
    closeLimit' (liftLipschitzRational q)
                (liftLipschitzApproximation g L φ)
                (liftLipschitzApproximationCauchy g L φ σ)
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

    α : g δ χ ≡
        liftLipschitzApproximation g L φ (L · δ) (0<· {x = L} {y = δ} φ χ)
    α = cong₂ g
              (sym $ ·/' L δ φ')
              (isProp→PathP
                (λ i → isProp< 0 (·/' L δ φ' (~ i)))
                χ
                (0</ {x = L · δ} {y = L} (0<· {x = L} {y = δ} φ χ) φ))

    ο' : Close
      ((L · ε) - (L · δ)) (fst ο)
      (liftLipschitzRational q)
      (liftLipschitzApproximation g L φ (L · δ) (0<· {x = L} {y = δ} φ χ))
    ο' = subst (Close _ _ _) α (snd ο)

  limitRationalCase :
    (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y)
    (g : (ε : ℚ) → 0 < ε → ℝ)
    (χ : CauchyApproximation'' ℝ (LiftLipschitzRelation L φ) g)
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
        (liftLipschitzApproximation g L φ)
        (liftLipschitzApproximationCauchy g L φ χ)
        (L · ε) (L · δ)
        (0<· {x = L} {y = ε} φ π) (0<· {x = L} {y = δ} φ ρ) (fst ο)
        (closeSymmetric
          (liftLipschitzApproximation g L φ
            (L · δ) (0<· {x = L} {y = δ} φ ρ))
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

    α : g δ ρ ≡
        liftLipschitzApproximation g L φ (L · δ) (0<· {x = L} {y = δ} φ ρ)
    α = cong₂ g
              (sym $ ·/' L δ φ')
              (isProp→PathP
                (λ i → isProp< 0 (·/' L δ φ' (~ i)))
                ρ
                (0</ {x = L · δ} {y = L} (0<· {x = L} {y = δ} φ ρ) φ))

    ο' : Close ((L · ε) - (L · δ)) (fst ο)
               (liftLipschitzApproximation
                 g L φ
                 (L · δ) (0<· {x = L} {y = δ} φ ρ))
               (liftLipschitzRational r)
    ο' = subst (λ ?x → Close _ (fst ο) ?x _) α (snd ο)

  limitLimitCase :
    (x y f g : (ε : ℚ) → 0 < ε → ℝ)
    (ω : CauchyApproximation x)
    (χ : CauchyApproximation y)
    (π : CauchyApproximation'' ℝ (LiftLipschitzRelation L φ) f)
    (ρ : CauchyApproximation'' ℝ (LiftLipschitzRelation L φ) g)
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
      (liftLipschitzApproximation f L φ)
      (liftLipschitzApproximation g L φ)
      (liftLipschitzApproximationCauchy f L φ π)
      (liftLipschitzApproximationCauchy g L φ ρ)
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

      ζ : f δ τ ≡
          liftLipschitzApproximation f L φ (L · δ) (0<· {x = L} {y = δ} φ τ)
      ζ = cong₂ f
                (sym $ ·/' L δ φ')
                (isProp→PathP
                  -- TODO: What on earth is going on here?
                  (λ i → isProp< 0 (·/' L δ φ' (~ i)))
                  τ
                  (0</ {x = L · δ} {y = L} (0<· {x = L} {y = δ} φ τ) φ))

      ι : g η υ ≡
          liftLipschitzApproximation g L φ (L · η) (0<· {x = L} {y = η} φ υ)
      ι = cong₂ g
                (sym $ ·/' L η φ')
                (isProp→PathP
                  (λ i → isProp< 0 (·/' L η φ' (~ i)))
                  υ
                  (0</ {x = L · η} {y = L} (0<· {x = L} {y = η} φ υ) φ))

      κ : Close ((L · ε) - ((L · δ) + (L · η))) (fst γ)
                (liftLipschitzApproximation f L φ (L · δ)
                  (0<· {x = L} {y = δ} φ τ))
                (liftLipschitzApproximation g L φ (L · η)
                  (0<· {x = L} {y = η} φ υ))
      κ = subst2 (Close _ _) ζ ι (snd γ)
