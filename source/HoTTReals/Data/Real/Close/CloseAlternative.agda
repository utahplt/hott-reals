module HoTTReals.Data.Real.Close.CloseAlternative where

import Cubical.Data.Bool as Bool
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close.ReflexiveSymmetric
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

Close'Σ : Σ ((ε : ℚ) → 0 < ε → ℝ → ℝ → Type ℓ-zero)
            (λ Close' →
            Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close' ε φ u v))
            (λ φ →
            Rounded Close' φ ×
            TriangleInequality₁ Close Close' squash φ))
Close'Σ =
  let
    bar = ψ , ω , bSeperated , χ , π , ρ , σ , bProposition
    foo = recursion {A = A} {B = B} bar
  in (λ ε φ u v → (fst $ foo u) v ε φ) ,
     ((λ ε φ u v → (fst $ snd $ foo u) v ε φ) ,
      (λ u v ε φ → (fst $ snd $ snd $ foo u) v ε φ) ,
      (λ u v w ε η ω θ →
       -- Oh my goodness
       flip $ (fst $ snd $ snd $ snd $ foo u) v w η ε θ ω))
      -- TODO: Update I don't think this works
      -- This one has eight cases according to the last paragraph of the proof
      -- Not included as as part of A'
      -- (λ u v w ε η ω θ →
      --   let foo' = (fst $ snd $ snd $ snd $ foo w) u v ε η ω θ
      --       foo'' = (snd $ snd $ snd $ snd $ foo u) v w ε η ω θ
      --   in {!!}))

      -- Update from later: I think it does, we just forgot to call recursion∼
      -- afterwords
  where
  A' : (ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero) → Type ℓ-zero
  A' ◆ = ((u : ℝ) (ε : ℚ) (φ : 0 < ε) → isProp (◆ u ε φ)) ×
         ((u : ℝ) (ε : ℚ) (ω : 0 < ε) →
          (◆ u ε ω) ↔ ∃ ℚ (λ θ → (0 < θ) ×
                                 Σ (0 < ε - θ)
                                   (λ χ → ◆ u (ε - θ) χ))) ×
         ((u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (θ : 0 < η) →
          Close ε ω u v →
          ◆ u η θ → ◆ v (η + ε) (0<+' {x = η} {y = ε} θ ω)) ×
         ((u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (θ : 0 < η) →
          Close ε ω u v →
          ◆ v η θ → ◆ u (η + ε) (0<+' {x = η} {y = ε} θ ω))

  A : Type (ℓ-suc ℓ-zero)
  A = Σ (ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero) A'

  B : A → A → (ε : ℚ) → 0 < ε → Type ℓ-zero
  B ◆ ♥ ε φ = (u : ℝ) (η : ℚ) (ψ : 0 < η) →
              ((fst ◆) u η ψ → (fst ♥) u (ε + η) (0<+' {x = ε} {y = η} φ ψ)) × 
              ((fst ♥) u η ψ → (fst ◆) u (ε + η) (0<+' {x = ε} {y = η} φ ψ))

  C' : ((ε : ℚ) → 0 < ε → Type ℓ-zero) → Type ℓ-zero
  C' ▲ =
    ((ε : ℚ) (φ : 0 < ε) → isProp (▲ ε φ)) ×
    ((ε : ℚ) (φ : 0 < ε) → ▲ ε φ ↔ ∃ ℚ (λ θ → (0 < θ) ×
                                              Σ (0 < ε - θ)
                                                (λ χ → ▲ (ε - θ) χ)))

  C : Type (ℓ-suc ℓ-zero)
  C = Σ ((ε : ℚ) → 0 < ε → Type ℓ-zero) C'

  D : C → C → (ε : ℚ) → 0 < ε → Type ℓ-zero
  D ▲ □ ε φ = (η : ℚ) (ψ : 0 < η) →
              ((fst ▲) η ψ → (fst □) (η + ε) (0<+' {x = η} {y = ε} ψ φ)) ×
              ((fst □) η ψ → (fst ▲) (η + ε) (0<+' {x = η} {y = ε} ψ φ))

  a'Proposition : (◆ : ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero) → isProp (A' ◆)
  -- Trick: hehe we need the first projection to prove the rest are
  -- propositions, so just assume it's here. This lemma says we can do that
  a'Proposition ◆ = isOfHLevelSucIfInhabited→isOfHLevelSuc 0
    (λ a → let β : (u : ℝ) (ε : ℚ) (φ : 0 < ε) → isProp (◆ u ε φ)
               β = fst a
           in isProp×3 (isPropΠ3 (λ _ _ _ → isPropIsProp))
                       (isPropΠ3 (λ u ε φ →
                         isProp× (isProp→ isPropPropTrunc)
                                 (isProp→ (β u ε φ))))
                       (isPropΠ6 (λ u v ε η ω θ →
                         isPropΠ2 (λ χ π →
                           β v (η + ε) (0<+' {x = η} {y = ε} θ ω))))
                       (isPropΠ6 λ u v ε η ω θ →
                         isPropΠ2 λ χ π →
                           β u (η + ε) (0<+' {x = η} {y = ε} θ ω)))

  bProposition : (◆ ♥ : A) (ε : ℚ) (φ : 0 < ε) → isProp (B ◆ ♥ ε φ)
  bProposition ◆ ♥ ε φ =
    isPropΠ3
      (λ u η ψ →
        isProp×
          (isProp→ ((fst $ snd ♥) u (ε + η) (0<+' {x = ε} {y = η} φ ψ)))
          (isProp→ ((fst $ snd ◆) u (ε + η) (0<+' {x = ε} {y = η} φ ψ))))

  c'Proposition : (▲ : (ε : ℚ) → 0 < ε → Type ℓ-zero) → isProp (C' ▲)
  c'Proposition ▲ = isOfHLevelSucIfInhabited→isOfHLevelSuc 0
    (λ c → let δ : (ε : ℚ) (φ : 0 < ε) → isProp (▲ ε φ)
               δ = fst c
           in isProp×
                (isPropΠ2 (λ _ _ → isPropIsProp))
                (isPropΠ2
                  (λ ε φ →
                    isProp×
                      (isProp→ isPropPropTrunc)
                      (isProp→ (δ ε φ)))))

  dProposition : (▲ ◻ : C) (ε : ℚ) (φ : 0 < ε) → isProp (D ▲ ◻ ε φ)
  dProposition ▲ ◻ ε φ =
    isPropΠ2 (λ η ψ →
      isProp×
        (isProp→ ((fst $ snd ◻) (η + ε) (0<+' {x = η} {y = ε} ψ φ)))
        (isProp→ ((fst $ snd ▲) (η + ε) (0<+' {x = η} {y = ε} ψ φ))))

  bSeperated : (◆ ♥ : A) → ((ε : ℚ) (φ : 0 < ε) → B ◆ ♥ ε φ) → ◆ ≡ ♥
  bSeperated ◆ ♥ χ =
    Σ≡Prop a'Proposition
           (funExt λ u → funExt (λ ε → funExt (λ φ → π u ε φ)))
    where
    π : (u : ℝ) (ε : ℚ) (φ : 0 < ε) → (fst ◆) u ε φ ≡ (fst ♥) u ε φ
    π u ε φ = ua $ propBiimpl→Equiv ((fst $ snd ◆) u ε φ)
                                    ((fst $ snd ♥) u ε φ)
                                    σ τ
      where
      -- TODO: Pull out into lemma
      ρ : (θ : ℚ) → θ + (ε - θ) ≡ ε
      ρ θ = θ + (ε - θ)
              ≡⟨ cong (_+_ θ) (+Comm ε (- θ)) ⟩
            θ + (- θ + ε)
              ≡⟨ +Assoc θ (- θ) ε ⟩
            (θ + - θ) + ε
              ≡⟨ cong (flip _+_ ε) (+InvR θ) ⟩
            0 + ε
              ≡⟨ +IdL ε ⟩
            ε ∎

      σ : (fst ◆) u ε φ → (fst ♥) u ε φ
      σ τ = μ
        where
        ι : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ τ → (fst ◆) u (ε - θ) τ))
        ι = (fst $ (fst $ snd $ snd ◆) u ε φ) τ

        κ : (θ : ℚ) →
             (0 < θ) × Σ (0 < ε - θ) (λ τ → (fst ◆) u (ε - θ) τ) →
             (fst ♥) u ε φ
        κ θ (τ , υ , γ) = ο
          where
          ν : (fst ♥) u (θ + (ε - θ)) (0<+' {x = θ} {y = ε - θ} τ υ)
          ν = (fst $ χ θ τ u (ε - θ) υ) $ γ

          ξ : Σ (0 < ε) (λ ι → (fst ♥) u ε ι)
          ξ = subst (λ ?x → Σ (0 < ?x) (λ ι → (fst ♥) u ?x ι))
                       (ρ θ)
                       (0<+' {x = θ} {y = ε - θ} τ υ , ν)

          ο : (fst ♥) u ε φ
          ο = subst (λ ?x → (fst ♥) u ε ?x)
                         (isProp< 0 ε (fst ξ) φ)
                         (snd ξ)

        μ : (fst ♥) u ε φ
        μ = ∃-rec ((fst $ snd ♥) u ε φ) κ ι

      τ : (fst ♥) u ε φ → (fst ◆) u ε φ
      τ υ = μ
        where
        ι : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (λ τ → (fst ♥) u (ε - θ) τ))
        ι = (fst $ (fst $ snd $ snd ♥) u ε φ) υ

        κ : (θ : ℚ) →
            (0 < θ) × Σ (0 < (ε - θ)) (λ υ → (fst ♥) u (ε - θ) υ) →
            (fst ◆) u ε φ
        κ θ (υ , γ , ζ) = ο
          where
          ν : (fst ◆) u (θ + (ε - θ)) (0<+' {x = θ} {y = ε - θ} υ γ)
          ν = (snd $ χ θ υ u (ε - θ) γ) $ ζ

          ξ : Σ (0 < ε) (λ ι → (fst ◆) u ε ι)
          ξ = subst (λ ?x → Σ (0 < ?x) (λ ι → (fst ◆) u ?x ι))
                       (ρ θ)
                       (0<+' {x = θ} {y = ε - θ} υ γ , ν)

          ο : (fst ◆) u ε φ
          ο = subst (λ ?x → (fst ◆) u ε ?x)
                         (isProp< 0 ε (fst ξ) φ)
                         (snd ξ)

        μ : (fst ◆) u ε φ
        μ = ∃-rec ((fst $ snd ◆) u ε φ) κ ι

  dSeperated : (▲ ◻ : C) → ((ε : ℚ) (φ : 0 < ε) → D ▲ ◻ ε φ) → ▲ ≡ ◻
  dSeperated ▲ ◻ φ =
    Σ≡Prop c'Proposition (funExt (λ ε → funExt (λ φ → ψ ε φ)))
    where
    ψ : (ε : ℚ) (φ : 0 < ε) → (fst ▲) ε φ ≡ (fst ◻) ε φ
    ψ ε ψ = ua $ propBiimpl→Equiv ((fst $ snd ▲) ε ψ)
                                  ((fst $ snd ◻) ε ψ)
                                  ω χ
      where
      ω : (fst ▲) ε ψ → (fst ◻) ε ψ
      ω χ = ∃-rec ((fst $ snd ◻) ε ψ) κ ι
        where
        ι : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) ((fst ▲) (ε - θ)))
        ι = (fst $ (snd $ snd ▲) ε ψ) χ

        κ : (θ : ℚ) →
            (0 < θ) × Σ (0 < (ε - θ)) (fst ▲ (ε - θ)) →
            (fst ◻) ε ψ
        κ θ (π , σ , τ) = μ
          where
          ν : (fst ◻) ((ε - θ) + θ) (0<+' {x = ε - θ} {y = θ} σ π)
          ν = (fst $ φ θ π (ε - θ) σ) τ

          ξ : Σ (0 < ε) ((fst ◻) ε)
          ξ = subst (λ ?x → Σ (0 < ?x) ((fst ◻) ?x))
                    (subtractAddRightCancel θ ε)
                    (0<+' {x = ε - θ} {y = θ} σ π , ν)

          μ : (fst ◻) ε ψ
          μ = subst ((fst ◻) ε) (isProp< 0 ε (fst ξ) ψ) (snd ξ) 
  
      χ : (fst ◻) ε ψ → (fst ▲) ε ψ
      χ π = ∃-rec ((fst $ snd ▲) ε ψ) κ ι
        where
        ι : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) ((fst ◻) (ε - θ)))
        ι = (fst $ (snd $ snd ◻) ε ψ) π

        κ : (θ : ℚ) →
            (0 < θ) × Σ (0 < (ε - θ)) (fst ◻ (ε - θ)) →
            (fst ▲) ε ψ
        κ θ (σ , τ , υ) = μ
          where
          ν : (fst ▲) ((ε - θ) + θ) (0<+' {x = ε - θ} {y = θ} τ σ)
          ν = (snd $ φ θ σ (ε - θ) τ) υ

          ξ : Σ (0 < ε) ((fst ▲) ε)
          ξ = subst (λ ?x → Σ (0 < ?x) ((fst ▲) ?x))
                    (subtractAddRightCancel θ ε)
                    ((0<+' {x = ε - θ} {y = θ} τ σ) , ν)

          μ : (fst ▲) ε ψ
          μ = subst ((fst ▲) ε) (isProp< 0 ε (fst ξ) ψ) (snd ξ)

  ψ : ℚ → A
  ψ q =
    let ξ = α , β , dSeperated , ζ , ι , κ , μ , dProposition
        ο = recursion {A = C} {B = D} ξ
        ο' = recursion∼ {A = C} {B = D} ξ
    in (λ u → fst $ ο u) ,
       ((λ u → fst $ snd $ ο u) ,
        (λ u → snd $ snd $ ο u) ,
        (λ u v ε θ φ ψ ω → fst $ ο' ω θ ψ) ,
        (λ u v ε θ φ ψ ω → snd $ ο' ω θ ψ))
    where
    Close'RationalRational : (r : ℚ) (ε : ℚ) → 0 < ε → Type ℓ-zero
    Close'RationalRational r ε φ = ∣ q - r ∣ < ε

    close'RationalRationalProposition : 
      (r : ℚ) (ε : ℚ) (φ : 0 < ε)  → isProp (Close'RationalRational r ε φ)
    close'RationalRationalProposition r ε φ = isProp< ∣ q - r ∣ ε

    close'RationalRationalOpen :
      (r : ℚ) (ε : ℚ) (φ : 0 < ε) →
      Close'RationalRational r ε φ →
      ∃ ℚ (λ θ → (0 < θ) ×
               Σ (0 < (ε - θ))
               (λ ψ → Close'RationalRational r (ε - θ) ψ))
    close'RationalRationalOpen r ε φ ψ = ∣ (∣∣<-open (q - r) ε φ ψ) ∣₁

    close'RationalRationalMonotone :
      (r : ℚ) (ε : ℚ) (φ : 0 < ε) →
      ∃ ℚ (λ θ → (0 < θ) ×
               Σ (0 < (ε - θ))
                 (Close'RationalRational r (ε - θ))) →
      Close'RationalRational r ε φ
    close'RationalRationalMonotone r ε φ ψ =
      ∃-rec (close'RationalRationalProposition r ε φ) ω ψ
      where
      ω : (θ : ℚ) →
          (0 < θ) × Σ (0 < (ε - θ)) (Close'RationalRational r (ε - θ)) → 
          Close'RationalRational r ε φ
      ω θ (χ , π , ρ) = isTrans< ∣ q - r ∣ (ε - θ) ε
                             ρ σ
        where
        σ : ε - θ < ε
        σ = subst (_<_ (ε - θ))
                       (+IdR ε)
                       (<-o+ (- θ) 0 ε (<antitone- {x = 0} {y = θ} χ))

    close'RationalRationalRounded :
      (r : ℚ) (ε : ℚ) (φ : 0 < ε) →
      Close'RationalRational r ε φ ↔
      ∃ ℚ (λ θ → (0 < θ) ×
               Σ (0 < (ε - θ))
               (λ ψ → Close'RationalRational r (ε - θ) ψ))
    close'RationalRationalRounded r ε φ =
      (close'RationalRationalOpen r ε φ ,
      close'RationalRationalMonotone r ε φ)

    α : ℚ → C
    α r = Close'RationalRational r ,
          (close'RationalRationalProposition r ,
           close'RationalRationalRounded r)

    Close'RationalLimit :
      (x : (ε : ℚ) → 0 < ε → ℝ)
      (φ : CauchyApproximation x)
      (f : (ε : ℚ) → 0 < ε → C)
      (ψ : CauchyApproximation'' C D f)
      (ε : ℚ) → 0 < ε → Type ℓ-zero
    Close'RationalLimit x φ f ψ ε ω =
      ∃ ℚ (λ δ → Σ (0 < δ)
          (λ χ → Σ (0 < ε - δ)
          -- The `q` is implicit in the construction of the output in `C`
          (λ π → (fst $ f δ χ) (ε - δ) π)))

    close'RationalLimitProposition :
      (x : (ε : ℚ) → 0 < ε → ℝ)
      (φ : CauchyApproximation x)
      (f : (ε : ℚ) → 0 < ε → C)
      (ψ : CauchyApproximation'' C D f)
      (ε : ℚ) (ω : 0 < ε) →
      isProp (Close'RationalLimit x φ f ψ ε ω)
    close'RationalLimitProposition x φ f ψ ε ω = isPropPropTrunc

    close'RationalLimitOpen :
      (x : (ε : ℚ) → 0 < ε → ℝ)
      (φ : CauchyApproximation x)
      (f : (ε : ℚ) → 0 < ε → C)
      (ψ : CauchyApproximation'' C D f)
      (ε : ℚ)
      (ω : 0 < ε) →
      Close'RationalLimit x φ f ψ ε ω →
      ∃ ℚ (λ θ → (0 < θ) ×
          Σ (0 < (ε - θ)) (Close'RationalLimit x φ f ψ (ε - θ)))
    close'RationalLimitOpen x φ f ψ ε ω = ∃-rec isPropPropTrunc χ
      where
      χ : (δ : ℚ) →
          Σ (0 < δ) (λ ω → Σ (0 < (ε - δ)) (fst (f δ ω) (ε - δ))) →
          ∃ ℚ
          (λ θ →
          (0 < θ) ×
          Σ (0 < (ε - θ))
          (λ χ →
          ∃ ℚ (λ η →
          Σ (0 < η)
          (λ π →
          Σ (0 < ((ε - θ) - η))
          (fst (f η π) ((ε - θ) - η))))))
      χ δ (χ , π , ρ) = ∃-rec isPropPropTrunc χ' σ
        where
          χ' : (θ : ℚ) →
               (0 < θ) × Σ (0 < ((ε - δ) - θ)) (fst (f δ χ) ((ε - δ) - θ)) →
               ∃ ℚ
               (λ θ →
               (0 < θ) ×
               Σ (0 < (ε - θ))
               (λ σ →
               ∃ ℚ
               (λ δ →
               Σ (0 < δ)
               (λ τ →
               Σ (0 < ((ε - θ) - δ))
               (fst (f δ τ) ((ε - θ) - δ))))))
          χ' θ (σ , τ , υ) =
            ∣ θ , (σ , ι' , ∣ δ , (χ , fst κ , snd κ) ∣₁) ∣₁
            where
            ζ : (ε - δ) - θ ≡ (ε - θ) - δ
            ζ = addLeftSwap ε (- δ) (- θ)

            ι : δ < (ε - θ)
            ι = 0<-→< {x = δ} {y = ε - θ} (subst (_<_ 0) ζ τ)

            ι' : 0 < (ε - θ)
            ι' = isTrans< 0 δ (ε - θ) χ ι

            κ : Σ (0 < (ε - θ) - δ) (fst (f δ χ) ((ε - θ) - δ))
            κ = subst (λ ?x → Σ (0 < ?x) (fst (f δ χ) ?x)) ζ (τ , υ)

          σ : ∃ ℚ (λ θ → (0 < θ) ×
                       Σ (0 < ((ε - δ) - θ))
                         (fst (f δ χ) ((ε - δ) - θ)))
          σ = (fst $ (snd $ snd $ f δ χ) (ε - δ) π) ρ

    close'RationalLimitMonotone : 
      (x : (ε : ℚ) → 0 < ε → ℝ)
      (φ : CauchyApproximation x)
      (f : (ε : ℚ) → 0 < ε → C)
      (ψ : CauchyApproximation'' C D f)
      (ε : ℚ)
      (ω : 0 < ε) →
      ∃ ℚ (λ θ → (0 < θ) ×
          Σ (0 < (ε - θ)) (Close'RationalLimit x φ f ψ (ε - θ))) →
      Close'RationalLimit x φ f ψ ε ω
    close'RationalLimitMonotone x φ f ψ ε ω χ =
      ∃-rec
        (close'RationalLimitProposition x φ f ψ ε ω)
        (λ θ (χ , π , ρ) →
          ∃-rec
            (close'RationalLimitProposition x φ f ψ ε ω)
            (λ δ (σ , τ , υ) →
              let ζ : (ε - θ) - δ ≡ (ε - δ) - θ 
                  ζ = addLeftSwap ε (- θ) (- δ)

                  ι : θ < ε - δ
                  ι = 0<-→< {x = θ} {y = ε - δ} (subst (_<_ 0) ζ τ)

                  ι' : 0 < ε - δ
                  ι' = isTrans< 0 θ (ε - δ) χ ι

                  κ : Σ (0 < (ε - δ) - θ) (fst (f δ σ) ((ε - δ) - θ))
                  κ = subst (λ ?x → Σ (0 < ?x) (fst (f δ σ) ?x))
                            ζ
                            (τ , υ)

                  μ : fst (f δ σ) (ε - δ) ι'
                  μ = snd
                    ((snd $ snd $ f δ σ) (ε - δ) ι')
                    (∣ θ , (χ , fst κ , snd κ) ∣₁)
              in ∣ δ , (σ , ι' , μ) ∣₁)
            ρ)
        χ

    close'RationalLimitRounded : 
      (x : (ε : ℚ) → 0 < ε → ℝ)
      (φ : CauchyApproximation x)
      (f : (ε : ℚ) → 0 < ε → C)
      (ψ : CauchyApproximation'' C D f)
      (ε : ℚ)
      (ω : 0 < ε) →
      Close'RationalLimit x φ f ψ ε ω ↔
      ∃ ℚ (λ θ → (0 < θ) ×
          Σ (0 < (ε - θ)) (Close'RationalLimit x φ f ψ (ε - θ)))
    close'RationalLimitRounded x φ f ψ ε ω =
      (close'RationalLimitOpen x φ f ψ ε ω) ,
      (close'RationalLimitMonotone x φ f ψ ε ω)

    β : (x : (ε : ℚ) → 0 < ε → ℝ)
        (φ : CauchyApproximation x)
        (f : (ε : ℚ) → 0 < ε → C)
        (ψ : CauchyApproximation'' C D f) →
        C
    β x φ f ψ = (Close'RationalLimit x φ f ψ) ,
                 (close'RationalLimitProposition x φ f ψ ,
                 close'RationalLimitRounded x φ f ψ)

    ζ : (r s ε : ℚ) (φ : 0 < ε) →
        (- ε) < (r - s) → (r - s) < ε →
        D (α r) (α s) ε φ
    ζ r s ε φ ψ ω η χ = ζ' , ζ''
      where
      ζ' : fst (α r) η χ → fst (α s) (η + ε) (0<+' {x = η} {y = ε} χ φ)
      ζ' ρ = isTrans≤<
        ∣ q - s ∣
        (∣ q - r ∣ + ∣ r - s ∣)
        (η + ε)
        (distanceTriangleInequality q r s)
        (+<+ {x = ∣ q - r ∣} {y = η} {z = ∣ r - s ∣} {w = ε}
          ρ (<→∣∣< {x = r - s} {ε = ε} ω ψ))

      ζ'' : fst (α s) η χ → fst (α r) (η + ε) (0<+' {x = η} {y = ε} χ φ)
      ζ'' ρ = isTrans≤<
        ∣ q - r ∣
        (∣ q - s ∣ + ∣ s - r ∣)
        (η + ε)
        (distanceTriangleInequality q s r)
        (+<+ {x = ∣ q - s ∣} {y = η} {z = ∣ s - r ∣} {w = ε}
          ρ (subst (flip _<_ ε)
                   (distanceCommutative r s)
                   (<→∣∣< {x = r - s} {ε = ε} ω ψ)))

    ξ :
      (r ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (ω : 0 < ε - δ)
      (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (π : CauchyApproximation'' C D g) →
      (θ : ℚ) (σ : 0 < θ) →
      ((η : ℚ) (τ : 0 < η) →
       fst (α r) η τ →
       fst (g δ ψ) (η + (ε - δ)) (0<+' {x = η} {y = ε - δ} τ ω)) →
      Close'RationalRational r θ σ →
      Close'RationalLimit y χ g π (θ + ε) (0<+' {x = θ} {y = ε} σ φ)
    ξ r ε δ φ ψ ω y χ g π θ σ ρ τ = ∣ δ , (ψ , fst υ , snd υ) ∣₁
      where
      υ : Σ (0 < (θ + ε) - δ) (fst (g δ ψ) ((θ + ε) - δ))
      υ = subst (λ ?x → Σ (0 < ?x) (fst (g δ ψ) ?x))
          (+Assoc θ ε (- δ))
            ((0<+' {x = θ} {y = ε - δ} σ ω) , ρ θ σ τ)

    ο :
      (r ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (ω : 0 < (ε - δ))
      (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (π : CauchyApproximation'' C D g) →
      (θ : ℚ) (σ : 0 < θ) →
      ((η : ℚ) (τ : 0 < η) →
       fst (g δ ψ) η τ →
       fst (α r) (η + (ε - δ)) (0<+' {x = η} {y = ε - δ} τ ω)) →
      Close'RationalLimit y χ g π θ σ →
      Close'RationalRational r (θ + ε) (0<+' {x = θ} {y = ε} σ φ)
    ο r ε δ φ ψ ω y χ g π θ σ ρ =
      ∃-rec (close'RationalRationalProposition
              r (θ + ε) (0<+' {x = θ} {y = ε} σ φ))
            ο'
      where
      ο' : (η : ℚ) →
           Σ (0 < η) (λ τ → Σ (0 < (θ - η)) (fst (g η τ) (θ - η))) →
           Close'RationalRational r (θ + ε) (0<+' {x = θ} {y = ε} σ φ)
      ο' η (τ , υ , ι) =
        subst (fst (α r) (θ + ε))
              (isProp< 0 (θ + ε) (fst μ) (0<+' {x = θ} {y = ε} σ φ))
              (snd μ) 
        where
        ζ' : 0 < (θ - η) + (δ + η) + (ε - δ)
        ζ' = 0<+' {x = (θ - η) + (δ + η)} {y = ε - δ}
                       (0<+' {x = θ - η} {y = δ + η}
                             υ
                             (0<+' {x = δ} {y = η} ψ τ))
                       ω

        α' : fst (g δ ψ) ((θ - η) + (δ + η))
                 (0<+' {x = θ - η} {y = δ + η} υ (0<+' {x = δ} {y = η} ψ τ)) →
             fst (α r) ((θ - η) + (δ + η) + (ε - δ)) ζ'
        α' = ρ ((θ - η) + (δ + η))
               (0<+' {x = θ - η} {y = δ + η} υ (0<+' {x = δ} {y = η} ψ τ))

        β' : fst (g η τ) (θ - η) υ →
             fst (g δ ψ) ((θ - η) + (δ + η))
                 (0<+' {x = θ - η} {y = δ + η} υ (0<+' {x = δ} {y = η} ψ τ))
        β' = snd $ π δ η ψ τ (θ - η) υ

        γ' : fst (α r) ((θ - η) + (δ + η) + (ε - δ)) ζ'
        γ' = α' $ β' ι

        κ : (θ - η) + (δ + η) + (ε - δ) ≡ θ + ε
        κ = (θ - η) + (δ + η) + (ε - δ)
              ≡⟨ cong (λ ?x → (θ - η) + ?x + (ε - δ)) (+Comm δ η) ⟩
            ((θ - η) + (η + δ)) + (ε - δ)
              ≡⟨ (sym $ +Assoc (θ - η) (η + δ) (ε - δ)) ⟩
            (θ - η) + ((η + δ) + (ε - δ))
              ≡⟨ cong (_+_ (θ - η)) (sym $ +Assoc η δ (ε - δ)) ⟩
            (θ - η) + (η + (δ + (ε - δ)))
              ≡⟨ cong (λ ?x → (θ - η) + (η + ?x)) (addLeftSubtractCancel δ ε) ⟩
            (θ - η) + (η + ε)
              ≡⟨ +Assoc (θ - η) η ε ⟩
            ((θ - η) + η) + ε
              ≡⟨ cong (flip _+_ ε) (subtractAddRightCancel η θ) ⟩
            θ + ε ∎

        μ : Σ (0 < θ + ε) (fst (α r) (θ + ε))
        μ = subst (λ ?x → Σ (0 < ?x) (fst (α r) ?x)) κ (ζ' , γ')

    ι : (r ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (ω : 0 < (ε - δ))
        (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y)
        (g : (ε : ℚ) → 0 < ε → C) (π : CauchyApproximation'' C D g) →
        (rational r) ∼[ ε - δ , ω ] (y δ ψ) →
        D (α r) (g δ ψ) (ε - δ) ω →
        D (α r) (β y χ g π) ε φ
    ι r ε δ φ ψ ω y χ g π ρ σ θ τ =
      ξ r ε δ φ ψ ω y χ g π θ τ σ'' ,
      ο r ε δ φ ψ ω y χ g π θ τ σ'
      where
      σ' : (η : ℚ) (τ : 0 < η) →
           fst (g δ ψ) η τ →
           fst (α r) (η + (ε - δ)) (0<+' {x = η} {y = ε - δ} τ ω)
      σ' η τ = snd $ σ η τ

      σ'' : (η : ℚ) (τ : 0 < η) →
            fst (α r) η τ →
            fst (g δ ψ) (η + (ε - δ)) (0<+' {x = η} {y = ε - δ} τ ω)
      σ'' η τ = fst $ σ η τ

    κ : (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
        (f : (ε : ℚ) → 0 < ε → C) (ψ : CauchyApproximation'' C D f)
        (r ε δ : ℚ) (ω : 0 < ε) (χ : 0 < δ) (π : 0 < ε - δ) →
        (x δ χ) ∼[ ε - δ , π ] (rational r) →
        D (f δ χ) (α r) (ε - δ) π →
        D (β x φ f ψ) (α r) ε ω
    κ x φ f ψ r ε δ ω χ π ρ σ θ τ =
      ο r ε δ ω χ π x φ f ψ θ τ σ' ,
      ξ r ε δ ω χ π x φ f ψ θ τ σ''
      where
      σ' : (η : ℚ) (τ : 0 < η) →
           fst (f δ χ) η τ →
           fst (α r) (η + (ε - δ)) (0<+' {x = η} {y = ε - δ} τ π)
      σ' η τ = fst $ σ η τ 

      σ'' : (η : ℚ) (τ : 0 < η) →
            fst (α r) η τ →
            fst (f δ χ) (η + (ε - δ)) (0<+' {x = η} {y = ε - δ} τ π)
      σ'' η τ = snd $ σ η τ

    ν : (x y : (ε : ℚ) → 0 < ε → ℝ) (f g : (ε : ℚ) → 0 < ε → C)
        (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
        (ω : CauchyApproximation'' C D f) (χ : CauchyApproximation'' C D g)
        (ε δ η : ℚ) (π : 0 < ε) (ρ : 0 < δ) (σ : 0 < η)
        (τ : 0 < (ε - (δ + η))) →
        (θ : ℚ) (υ : 0 < θ) →
        ((ϕ : ℚ) (ξ : 0 < ϕ) →
         (fst (f δ ρ) ϕ ξ) →
         (fst (g η σ) (ϕ + (ε - (δ + η)))
           (0<+' {x = ϕ} {y = ε - (δ + η)} ξ τ))) →
        Close'RationalLimit x φ f ω θ υ →
        Close'RationalLimit y ψ g χ (θ + ε) (0<+' {x = θ} {y = ε} υ π)
    ν x y f g φ ψ ω χ ε δ η π ρ σ τ θ υ α =
      ∃-rec
        (close'RationalLimitProposition
          y ψ g χ (θ + ε) (0<+' {x = θ} {y = ε} υ π))
        ν'
      where
      ν' : (κ : ℚ) →
           (Σ (0 < κ) (λ β → Σ (0 < θ - κ) (λ γ → fst (f κ β) (θ - κ) γ))) →
           Close'RationalLimit y ψ g χ (θ + ε) (0<+' {x = θ} {y = ε} υ π)
      ν' κ (β , γ , ζ) = ∣ η , (σ , fst μ' , snd μ') ∣₁
        where
        ι' : fst (f δ ρ) ((θ - κ) + (κ + δ))
                 (0<+' {x = (θ - κ)} {y = (κ + δ)} γ (0<+' {x = κ} {y = δ} β ρ))
        ι' = (fst $ ω κ δ β ρ (θ - κ) γ) ζ

        ξ' = (0<+' {x = (θ - κ) + (κ + δ)} {y = ε - (δ + η)}
                (0<+' {x = θ - κ} {y = κ + δ} γ (0<+' {x = κ} {y = δ} β ρ))
                τ)

        ο' : (θ - κ) + (κ + δ) + (ε - (δ + η)) ≡ ((θ + ε) - η)
        ο' = (θ - κ) + (κ + δ) + (ε - (δ + η))
               ≡⟨ cong (flip _+_ (ε - (δ + η))) (+Assoc (θ - κ) κ δ) ⟩
             (((θ - κ) + κ) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → (?x + δ) + (ε - (δ + η)))
                       (sym $ +Assoc θ (- κ) κ) ⟩
             ((θ + (- κ + κ)) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → ((θ + ?x) + δ) + (ε - (δ + η))) (+InvL κ) ⟩
             ((θ + 0) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → (?x + δ) + (ε - (δ + η))) (+IdR θ) ⟩
             (θ + δ) + (ε - (δ + η))
               ≡⟨ (sym $ +Assoc θ δ (ε - (δ + η))) ⟩
             θ + (δ + (ε - (δ + η)))
               ≡⟨ cong (_+_ θ) (+Assoc δ ε (- (δ + η))) ⟩
             θ + ((δ + ε) - (δ + η))
               ≡⟨ cong (λ ?x → θ + ((δ + ε) + ?x)) (negateAdd δ η) ⟩
             θ + ((δ + ε) + ((- δ) + (- η)))
               ≡⟨ cong (_+_ θ) (+Assoc (δ + ε) (- δ) (- η)) ⟩
             θ + (((δ + ε) + (- δ)) + (- η))
               ≡⟨ cong (λ ?x → θ + (?x + (- η))) (addSubtractLeftCancel δ ε) ⟩
             θ + (ε + (- η))
               ≡⟨ +Assoc θ ε (- η) ⟩
             ((θ + ε) - η) ∎

        μ : fst (g η σ) ((θ - κ) + (κ + δ) + (ε - (δ + η))) ξ'
              
        μ = α ((θ - κ) + (κ + δ))
              (0<+' {x = θ - κ} {y = κ + δ} γ
                (0<+' {x = κ} {y = δ} β ρ))
              ι'
        
        μ' : Σ (0 < (θ + ε) - η) (fst (g η σ) ((θ + ε) - η))
        μ' = subst (λ ?x → Σ (0 < ?x) (fst (g η σ) ?x)) ο' (ξ' , μ) 

    μ : (x y : (ε : ℚ) → 0 < ε → ℝ) (f g : (ε : ℚ) → 0 < ε → C)
        (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
        (ω : CauchyApproximation'' C D f) (χ : CauchyApproximation'' C D g)
        (ε δ η : ℚ) (π : 0 < ε) (ρ : 0 < δ) (σ : 0 < η)
        (τ : 0 < (ε - (δ + η))) →
        (x δ ρ) ∼[ ε - (δ + η) , τ ] (y η σ) →
        D (f δ ρ) (g η σ) (ε - (δ + η)) τ →
        D (β x φ f ω) (β y ψ g χ) ε π
    μ x y f g φ ψ ω χ ε δ η π ρ σ τ υ ι θ κ =
      (ν x y f g φ ψ ω χ ε δ η π ρ σ τ θ κ υ') ,
      (ν y x g f ψ φ χ ω ε η δ π σ ρ α' θ κ υ'')
      where
      υ' : (ϕ : ℚ) (ξ : 0 < ϕ) →
            fst (f δ ρ) ϕ ξ →
            fst (g η σ) (ϕ + (ε - (δ + η)))
              (0<+' {x = ϕ} {y = ε - (δ + η)} ξ τ)
      υ' ϕ ξ = fst $ ι ϕ ξ

      α' : 0 < ε - (η + δ)
      α' = subst (λ ?x → 0 < ε - ?x) (+Comm δ η) τ

      υ'' : (ϕ : ℚ) (ξ : 0 < ϕ) →
            fst (g η σ) ϕ ξ →
            fst (f δ ρ) (ϕ + (ε - (η + δ)))
              (0<+' {x = ϕ} {y = ε - (η + δ)} ξ α')
      υ'' ϕ ξ = β' ∘ (snd $ ι ϕ ξ)
        where
        β' : fst (f δ ρ) (ϕ + (ε - (δ + η)))
               (0<+' {x = ϕ} {y = ε - (δ + η)} ξ τ) →
             fst (f δ ρ) (ϕ + (ε - (η + δ)))
               (0<+' {x = ϕ} {y = ε - (η + δ)} ξ α')
        β' γ' = ζ''
          where
          ζ' : Σ (0 < ϕ + (ε - (η + δ))) (fst (f δ ρ) (ϕ + (ε - (η + δ))))
          ζ' = subst (λ ?x → Σ (0 < ϕ + (ε - ?x)) (fst (f δ ρ) (ϕ + (ε - ?x))))
                     (+Comm δ η)
                     ((0<+' {x = ϕ} {y = ε - (δ + η)} ξ τ) , γ')

          ζ'' : fst (f δ ρ) (ϕ + (ε - (η + δ)))
                  (0<+' {x = ϕ} {y = ε - (η + δ)} ξ α')
          ζ'' = subst (fst (f δ ρ) (ϕ + (ε - (η + δ))))
                      (isProp< 0 (ϕ + (ε - (η + δ)))
                        (fst ζ') (0<+' {x = ϕ} {y = ε - (η + δ)} ξ α'))
                      (snd ζ')

  ω : (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
      (f : (ε : ℚ) → 0 < ε → A) (ψ : CauchyApproximation'' A B f) →
      A
  ω x φ f ψ =
    let ξ = α , β , dSeperated , ζ , ι , κ , μ , dProposition
        ο = recursion {A = C} {B = D} ξ
        ο' = recursion∼ {A = C} {B = D} ξ
    in (λ u → fst $ ο u) ,
       ((λ u → fst $ snd $ ο u) ,
        (λ u → snd $ snd $ ο u) ,
        (λ u v ε θ φ ψ ω → fst $ ο' ω θ ψ) ,
        (λ u v ε θ φ ψ ω → snd $ ο' ω θ ψ))
    where
    Close'LimitRational :
      (r : ℚ)
      (ε : ℚ) → 0 < ε → Type ℓ-zero
    Close'LimitRational r ε ψ =
      ∃ ℚ (λ δ → Σ (0 < δ)
          (λ ω → Σ (0 < ε - δ)
          (λ χ → (fst $ f δ ω) (rational r) (ε - δ) χ)))

    close'LimitRationalProposition :
      (r : ℚ)
      (ε : ℚ) (ψ : 0 < ε) →
      isProp (Close'LimitRational r ε ψ)
    close'LimitRationalProposition r ε ψ = isPropPropTrunc

    close'LimitRationalOpen :
      (r : ℚ)
      (ε : ℚ)
      (ω : 0 < ε) →
      Close'LimitRational r ε ω →
      ∃ ℚ (λ θ → (0 < θ) ×
          Σ (0 < (ε - θ)) (Close'LimitRational r (ε - θ)))
    close'LimitRationalOpen r ε ω =
      ∃-rec isPropPropTrunc χ
      where
      χ : (δ : ℚ) →
          Σ (0 < δ)
          (λ π → Σ (0 < (ε - δ)) ((fst (f δ π)) (rational r) (ε - δ))) →
          ∃ ℚ
          (λ θ →
          (0 < θ) ×
          Σ (0 < (ε - θ))
          (λ σ →
          ∃ ℚ (λ η →
          Σ (0 < η)
          (λ τ →
          Σ (0 < ((ε - θ) - η)) (fst (f η τ) (rational r) ((ε - θ) - η))))))
      χ δ (π , ρ , σ) = ∃-rec isPropPropTrunc χ' τ
        where
        χ' : (θ' : ℚ) →
             (0 < θ') ×
             Σ (0 < ((ε - δ) - θ')) (fst (f δ π) (rational r) ((ε - δ) - θ')) →
             ∃ ℚ
             (λ θ →
             (0 < θ) ×
             Σ (0 < (ε - θ))
             (λ σ' →
             ∃ ℚ
             (λ η →
             Σ (0 < η)
             (λ τ →
             Σ (0 < ((ε - θ) - η)) (fst (f η τ) (rational r) ((ε - θ) - η))))))
        χ' θ (τ , υ , ο) =
          ∣ θ , (τ , ι' , ∣ δ , (π , fst κ , snd κ) ∣₁) ∣₁
          where
          ζ : (ε - δ) - θ ≡ (ε - θ) - δ
          ζ = addLeftSwap ε (- δ) (- θ)

          ι : δ < ε - θ
          ι = 0<-→< {x = δ} {y = ε - θ} (subst (_<_ 0) ζ υ)

          ι' : 0 < ε - θ
          ι' = isTrans< 0 δ (ε - θ) π ι

          κ : Σ (0 < (ε - θ) - δ) (fst (f δ π) (rational r) ((ε - θ) - δ))
          κ = subst (λ ?x → Σ (0 < ?x) (fst (f δ π) (rational r) ?x)) ζ (υ , ο)

        τ : ∃ ℚ (λ θ → (0 < θ) ×
                     Σ (0 < ((ε - δ) - θ))
                       (fst (f δ π) (rational r) ((ε - δ) - θ)))
        τ = fst ((fst $ snd $ snd $ f δ π) (rational r) (ε - δ) ρ) σ

    close'LimitRationalMonotone : 
      (r : ℚ)
      (ε : ℚ)
      (ω : 0 < ε) →
      ∃ ℚ (λ θ → (0 < θ) ×
          Σ (0 < (ε - θ)) (Close'LimitRational r (ε - θ))) →
      Close'LimitRational r ε ω
    close'LimitRationalMonotone r ε ω =
      ∃-rec
        (close'LimitRationalProposition r ε ω)
        (λ θ (χ , π , ρ) → ∃-rec
          (close'LimitRationalProposition r ε ω)
          (λ δ (σ , τ , υ) →
            let ζ : (ε - θ) - δ ≡ (ε - δ) - θ
                ζ = addLeftSwap ε (- θ) (- δ)

                ι : θ < ε - δ
                ι = 0<-→< {x = θ} {y = ε - δ} (subst (_<_ 0) ζ τ) 

                ι' : 0 < ε - δ
                ι' = isTrans< 0 θ (ε - δ) χ ι

                κ : Σ (0 < (ε - δ) - θ)
                      (fst (f δ σ) (rational r) ((ε - δ) - θ))
                κ = subst (λ ?x → Σ (0 < ?x) (fst (f δ σ) (rational r) ?x))
                          ζ
                          (τ , υ)

                μ : fst (f δ σ) (rational r) (ε - δ) ι'
                μ = (snd $ (fst $ snd $ snd $ f δ σ) (rational r) (ε - δ) ι')
                      (∣ θ , (χ , fst κ , snd κ) ∣₁)
            in ∣ δ , (σ , ι' , μ) ∣₁)
          ρ)

    close'LimitRationalRounded :
      (r : ℚ) →
      (ε : ℚ) (ψ : 0 < ε) →
      Close'LimitRational r ε ψ ↔
      ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (Close'LimitRational r (ε - θ)))
    close'LimitRationalRounded r ε ψ =
      close'LimitRationalOpen r ε ψ ,
      close'LimitRationalMonotone r ε ψ

    α : ℚ → C
    α r = Close'LimitRational r ,
          (close'LimitRationalProposition r , close'LimitRationalRounded r)

    -- See note in `Recursion` limit case. This is an example of where we need
    -- access to `y` and not just `g`.
    Close'LimitLimit :
      (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (ω : CauchyApproximation'' C D g)
      (ε : ℚ) → 0 < ε → Type ℓ-zero
    Close'LimitLimit y ψ g ω ε χ =
      ∃ (ℚ × ℚ)
        (λ where (δ , η) → Σ (0 < δ)
                    (λ π → Σ (0 < η)
                    (λ σ → Σ (0 < ε - (δ + η))
                    (λ τ → (fst $ f δ π) (y η σ) (ε - (δ + η)) τ))))

    close'LimitLimitProposition :
      (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (ω : CauchyApproximation'' C D g)
      (ε : ℚ) (χ : 0 < ε) →
      isProp (Close'LimitLimit y ψ g ω ε χ)
    close'LimitLimitProposition y ψ g ω ε χ = isPropPropTrunc

    close'LimitLimitOpen :
      (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (ω : CauchyApproximation'' C D g)
      (ε : ℚ) (χ : 0 < ε) →
      Close'LimitLimit y ψ g ω ε χ →
      ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (Close'LimitLimit y ψ g ω (ε - θ)))
    close'LimitLimitOpen y ψ g ω ε χ = ∃-rec isPropPropTrunc π
      where
      π : (δη : ℚ × ℚ) →
          let δ = fst δη
              η = snd δη
          in Σ (0 < (fst δη))
             (λ π →
             Σ (0 < (snd δη))
             (λ σ →
             Σ (0 < (ε - (δ + η))) (fst (f δ π) (y η σ) (ε - (δ + η))))) →
          ∃ ℚ
            (λ θ → (0 < θ) ×
                 Σ (0 < (ε - θ))
                   (Close'LimitLimit y ψ g ω (ε - θ)))
      π (δ , η) (π , ρ , σ , τ) = ∃-rec isPropPropTrunc π' υ
        where
        π' : (θ : ℚ) →
             (0 < θ) ×
             Σ (0 < ((ε - (δ + η)) - θ))
             (fst (f δ π) (y η ρ) ((ε - (δ + η)) - θ)) →
             ∃ ℚ
             (λ θ' → (0 < θ') ×
             Σ (0 < (ε - θ'))
             (Close'LimitLimit y ψ g ω (ε - θ')))
        π' θ (υ , ο , ξ) =
          ∣ θ , υ , ι' , ∣ (δ , η) , (π , ρ , fst κ , snd κ) ∣₁ ∣₁
          where
          ζ : (ε - (δ + η)) - θ ≡ (ε - θ) - (δ + η)
          ζ = addLeftSwap ε (- (δ + η)) (- θ)

          ι : (δ + η) < ε - θ
          ι = 0<-→< {x = δ + η} {y = ε - θ} (subst (_<_ 0) ζ ο)

          ι' : 0 < ε - θ
          ι' = isTrans< 0 (δ + η) (ε - θ) (0<+' {x = δ} {y = η} π ρ) ι

          κ : Σ (0 < (ε - θ) - (δ + η))
                (fst (f δ π) (y η ρ) ((ε - θ) - (δ + η)))
          κ = subst (λ ?x → Σ (0 < ?x) (fst (f δ π) (y η ρ) ?x)) ζ (ο , ξ)

        υ : ∃ ℚ
            (λ θ →
            (0 < θ) ×
            Σ (0 < ((ε - (δ + η)) - θ))
            (fst (f δ π) (y η ρ) ((ε - (δ + η)) - θ)))
        υ = fst ((fst $ snd $ snd $ f δ π) (y η ρ) (ε - (δ + η)) σ) τ

    close'LimitLimitMonotone :
      (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (ω : CauchyApproximation'' C D g)
      (ε : ℚ) (χ : 0 < ε) →
      ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (Close'LimitLimit y ψ g ω (ε - θ))) →
      Close'LimitLimit y ψ g ω ε χ
    close'LimitLimitMonotone y ψ g ω ε χ =
      ∃-rec
        (close'LimitLimitProposition y ψ g ω ε χ)
        (λ θ (π , ρ , σ) →
          ∃-rec
            (close'LimitLimitProposition y ψ g ω ε χ)
            (λ (δ , η) (τ , υ , ο , ξ) →
              let ζ : (ε - θ) - (δ + η) ≡ (ε - (δ + η)) - θ 
                  ζ = addLeftSwap ε (- θ) (- (δ + η))

                  κ : Σ (0 < (ε - (δ + η)) - θ)
                        (fst (f δ τ) (y η υ) ((ε - (δ + η)) - θ))
                  κ = subst (λ ?x → Σ (0 < ?x) (fst (f δ τ) (y η υ) ?x))
                            ζ
                            (ο , ξ)

                  ι : θ < ε - (δ + η)
                  ι = 0<-→< {x = θ} {y = ε - (δ + η)} (fst κ)

                  ι' : 0 < ε - (δ + η)
                  ι' = isTrans< 0 θ (ε - (δ + η)) π ι

                  μ : fst (f δ τ) (y η υ) (ε - (δ + η)) ι'
                  μ = (snd $ (fst $ snd $ snd $ f δ τ) (y η υ) (ε - (δ + η)) ι')
                      ∣ θ , (π , fst κ , snd κ) ∣₁
              in ∣ (δ , η) , (τ , υ , ι' , μ) ∣₁)
            σ)

    close'LimitLimitRounded :
      (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → C) (ω : CauchyApproximation'' C D g)
      (ε : ℚ) (χ : 0 < ε) →
      Close'LimitLimit y ψ g ω ε χ ↔
      ∃ ℚ (λ θ → (0 < θ) × Σ (0 < (ε - θ)) (Close'LimitLimit y ψ g ω (ε - θ)))
    close'LimitLimitRounded y ψ g ω ε χ =
      close'LimitLimitOpen y ψ g ω ε χ ,
      close'LimitLimitMonotone y ψ g ω ε χ

    β : (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
        (g : (ε : ℚ) → 0 < ε → C) (ω : CauchyApproximation'' C D g) →
        C
    β y ψ g ω = Close'LimitLimit y ψ g ω ,
                (close'LimitLimitProposition y ψ g ω ,
                (close'LimitLimitRounded y ψ g ω))

    ξ : (r s ε : ℚ) (φ' : 0 < ε)
        (ψ' : - ε < r - s) (ω : r - s < ε)
        (η : ℚ) (χ : 0 < η) →
        Close'LimitRational r η χ →
        Close'LimitRational s (η + ε) (0<+' {x = η} {y = ε} χ φ')
    ξ r s ε φ' ψ' ω η χ =
      ∃-rec (close'LimitRationalProposition
              s (η + ε) (0<+' {x = η} {y = ε} χ φ'))
            ξ'
      where
      ξ' : (θ : ℚ) →
           Σ (0 < θ)
             (λ π → Σ (0 < (η - θ)) (fst (f θ π) (rational r) (η - θ))) →
           Close'LimitRational s (η + ε) (0<+' {x = η} {y = ε} χ φ')
      ξ' θ (π , ρ , σ) = ∣ θ , (π , fst υ' , snd υ') ∣₁
        where
        τ :
          (u v : ℝ) (ε ϕ : ℚ)
          (τ : 0 < ε) (υ : 0 < ϕ) →
          Close ε τ u v →
          fst (f θ π) u ϕ υ →
          fst (f θ π) v (ϕ + ε) (0<+' {x = ϕ} {y = ε} υ τ)
        τ = fst $ snd $ snd $ snd (f θ π)

        υ : fst (f θ π) (rational s) ((η - θ) + ε)
                     (0<+' {x = η - θ} {y = ε} ρ φ')
        υ = τ (rational r) (rational s) ε
              (η - θ) φ' ρ
              (rationalRational r s ε φ' ψ' ω)
              σ

        υ' : Σ (0 < (η + ε) - θ) (fst (f θ π) (rational s) ((η + ε) - θ))
        υ' = subst (λ ?x → Σ (0 < ?x) (fst (f θ π) (rational s) ?x))
                   (addLeftSwap η (- θ) ε)
                   ((0<+' {x = η - θ} {y = ε} ρ φ') , υ)

    ζ : (r s ε : ℚ) (φ : 0 < ε) →
        (- ε) < (r - s) → (r - s) < ε → D (α r) (α s) ε φ
    ζ r s ε φ ψ ω η χ =
      ξ r s ε φ ψ ω η χ ,
      ξ s r ε φ ω' ψ' η χ
      where
      ω' : - ε < s - r
      ω' = subtract<→negate<subtract r s ε ω

      ψ' : s - r < ε
      ψ' = negate<subtract→subtract< s r ε ψ

    ο : (r ε δ : ℚ) (φ' : 0 < ε) (ψ' : 0 < δ) (ω : 0 < (ε - δ))
        (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y)
        (g : (ε : ℚ) → 0 < ε → C) (π : CauchyApproximation'' C D g)
        (η : ℚ) (ρ : 0 < η) →
        (rational r) ∼[ ε - δ , ω ] (y δ ψ') →
        Close'LimitRational r η ρ →
        Close'LimitLimit y χ g π (η + ε) (0<+' {x = η} {y = ε} ρ φ')
    ο r ε δ φ' ψ' ω y χ g π η ρ σ =
      ∃-rec (close'LimitLimitProposition
              y χ g π (η + ε) (0<+' {x = η} {y = ε} ρ φ'))
            ο'
      where
      ο' : (θ : ℚ) →
           Σ (0 < θ) (λ α → Σ (0 < η - θ) (fst (f θ α) (rational r) (η - θ))) →
           Close'LimitLimit y χ g π (η + ε) (0<+' {x = η} {y = ε} ρ φ')
      ο' θ (α , β , γ) = ∣ (θ , δ) , (α , ψ' , fst μ , snd μ) ∣₁
        where
        ζ' : (u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (χ : 0 < η) →
             Close ε ω u v →
             fst (f θ α) u η χ →
             fst (f θ α) v (η + ε) (0<+' {x = η} {y = ε} χ ω)
        ζ' = fst $ snd $ snd $ snd $ f θ α

        ι : fst (f θ α) (y δ ψ') ((η - θ) + (ε - δ))
                (0<+' {x = η - θ} {y = ε - δ} β ω)
        ι = ζ' (rational r) (y δ ψ') (ε - δ) (η - θ) ω β σ γ

        κ : (η - θ) + (ε - δ) ≡ (η + ε) - (θ + δ)
        κ = (η - θ) + (ε - δ)
              ≡⟨ +Assoc (η - θ) ε (- δ) ⟩
            ((η - θ) + ε) - δ
              ≡⟨ cong (flip _-_ δ) (addLeftSwap η (- θ) ε) ⟩
            ((η + ε) - θ) - δ
              ≡⟨ (sym $ +Assoc (η + ε) (- θ) (- δ)) ⟩
            (η + ε) + (- θ + - δ)
              ≡⟨ cong (_+_ (η + ε)) (sym $ negateAdd θ δ) ⟩
            (η + ε) - (θ + δ) ∎

        μ : Σ (0 < (η + ε) - (θ + δ))
                  (fst (f θ α) (y δ ψ') (((η + ε) - (θ + δ))))
        μ = subst (λ ?x → Σ (0 < ?x) (fst (f θ α) (y δ ψ') ?x))
                  κ
                  ((0<+' {x = η - θ} {y = ε - δ} β ω) , ι)

    ν : (r ε δ : ℚ) (φ' : 0 < ε) (ψ' : 0 < δ) (ω : 0 < (ε - δ))
        (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y)
        (g : (ε : ℚ) → 0 < ε → C) (π : CauchyApproximation'' C D g)
        (η : ℚ) (ρ : 0 < η) →
        (y δ ψ') ∼[ ε - δ , ω ]  (rational r) →
        Close'LimitLimit y χ g π η ρ →
        Close'LimitRational r (η + ε) (0<+' {x = η} {y = ε} ρ φ')
    ν r ε δ φ' ψ' ω y χ g π η ρ σ =
      ∃-rec (close'LimitRationalProposition
               r (η + ε) (0<+' {x = η} {y = ε} ρ φ'))
            ν'
      where
      ν' : (θϕ : ℚ × ℚ) →
           Σ (0 < fst θϕ)
             (λ τ →
             Σ (0 < snd θϕ)
             (λ υ →
             Σ (0 < η - (fst θϕ + snd θϕ))
             (fst (f (fst θϕ) τ)
                  (y (snd θϕ) υ)
                  (η - (fst θϕ + snd θϕ))))) →
           Close'LimitRational r (η + ε) (0<+' {x = η} {y = ε} ρ φ')
      ν' (θ , ϕ) (τ , υ , α , β) = ∣ θ , (τ , fst μ , snd μ) ∣₁
        where
        γ : (y ϕ υ) ∼[ ϕ + δ , 0<+' {x = ϕ} {y = δ} υ ψ' ] (y δ ψ')
        γ = χ ϕ δ υ ψ'

        ζ' : (u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (θ' : 0 < η) →
             Close ε ω u v →
             fst (f θ τ) u η θ' →
             fst (f θ τ) v (η + ε) (0<+' {x = η} {y = ε} θ' ω)
        ζ' = fst $ snd $ snd $ snd $ f θ τ 

        ι : fst (f θ τ) (y δ ψ') ((η - (θ + ϕ)) + (ϕ + δ))
            (0<+' {x = η - (θ + ϕ)} {y = ϕ + δ} α (0<+' {x = ϕ} {y = δ} υ ψ'))
        ι = ζ' (y ϕ υ) (y δ ψ') (ϕ + δ) (η - (θ + ϕ))
              (0<+' {x = ϕ} {y = δ} υ ψ') α γ β

        ι' : fst (f θ τ) (rational r) ((η - (θ + ϕ)) + (ϕ + δ) + (ε - δ))
             (0<+' {x = (η - (θ + ϕ)) + (ϕ + δ)} {y = ε - δ}
               (0<+' {x = η - (θ + ϕ)} {y = ϕ + δ} α
                 (0<+' {x = ϕ} {y = δ} υ ψ')) ω)
        ι' = ζ' (y δ ψ') (rational r) (ε - δ)
                ((η - (θ + ϕ)) + (ϕ + δ))
                ω
                (0<+' {x = η - (θ + ϕ)} {y = ϕ + δ}
                  α
                  (0<+' {x = ϕ} {y = δ} υ ψ'))
                σ ι

        κ : (η - (θ + ϕ)) + (ϕ + δ) + (ε - δ) ≡ (η + ε) - θ
        κ = ((η - (θ + ϕ)) + (ϕ + δ)) + (ε - δ)
              ≡⟨ cong (λ ?x → ((η + ?x) + (ϕ + δ)) + (ε - δ)) (negateAdd θ ϕ) ⟩
            ((η + ((- θ) + (- ϕ))) + (ϕ + δ)) + (ε - δ)
              ≡⟨ cong (λ ?x → ?x + (ε - δ))
                      (sym $ +Assoc η ((- θ) + (- ϕ)) (ϕ + δ)) ⟩
            (η + (((- θ) + (- ϕ)) + (ϕ + δ))) + (ε - δ)
              ≡⟨ cong (λ ?x → (η + ?x) + (ε - δ))
                      (sym $ +Assoc (- θ) (- ϕ) (ϕ + δ)) ⟩
            (η + ((- θ) + ((- ϕ) + (ϕ + δ)))) + (ε - δ)
              ≡⟨ cong (λ ?x → (η + ((- θ) + ?x)) + (ε - δ)) (+Assoc (- ϕ) ϕ δ) ⟩
            (η + ((- θ) + (((- ϕ) + ϕ) + δ))) + (ε - δ)
              ≡⟨ cong (λ ?x → (η + ((- θ) + (?x + δ))) + (ε - δ)) (+InvL ϕ) ⟩
            (η + ((- θ) + (0 + δ))) + (ε - δ)
              ≡⟨ cong (λ ?x → (η + ((- θ) + ?x)) + (ε - δ)) (+IdL δ) ⟩
            (η + ((- θ) + δ)) + (ε - δ)
              ≡⟨ (sym $ +Assoc η ((- θ) + δ) (ε - δ)) ⟩
            η + (((- θ) + δ) + (ε - δ))
              ≡⟨ cong (_+_ η) (sym $ +Assoc (- θ) δ (ε - δ)) ⟩
            η + ((- θ) + (δ + (ε - δ)))
              ≡⟨ cong (λ ?x → η + ((- θ) + ?x)) (addRightSwap δ ε (- δ)) ⟩
            η + ((- θ) + (ε + (δ - δ)))
              ≡⟨ cong (λ ?x → η + ((- θ) + (ε + ?x))) (+InvR δ) ⟩
            η + ((- θ) + (ε + 0))
              ≡⟨ cong (λ ?x → η + ((- θ) + ?x)) (+IdR ε) ⟩
            η + ((- θ) + ε)
              ≡⟨ cong (_+_ η) (+Comm (- θ) ε) ⟩
            η + (ε + (- θ))
              ≡⟨ +Assoc η ε (- θ) ⟩
            (η + ε) + (- θ) ∎
        
        μ : Σ (0 < (η + ε) - θ)
                   (fst (f θ τ) (rational r) ((η + ε) - θ))
        μ = subst (λ ?x → Σ (0 < ?x) (fst (f θ τ) (rational r) ?x))
                  κ
                  ((0<+' {x = (η - (θ + ϕ)) + (ϕ + δ)} {y = ε - δ}
                     (0<+' {x = η - (θ + ϕ)} {y = ϕ + δ}
                     α (0<+' {x = ϕ} {y = δ} υ ψ')) ω),
                   ι')

    ι : (r ε δ : ℚ) (φ' : 0 < ε) (ψ' : 0 < δ) (ω : 0 < (ε - δ))
        (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y)
        (g : (ε : ℚ) → 0 < ε → C) (π : CauchyApproximation'' C D g) →
        (rational r) ∼[ ε - δ , ω ] (y δ ψ') →
        D (α r) (g δ ψ') (ε - δ) ω →
        D (α r) (β y χ g π) ε φ'
    ι r ε δ φ' ψ' ω y χ g π ρ σ η τ =
      ο r ε δ φ' ψ' ω y χ g π η τ ρ ,
      ν r ε δ φ' ψ' ω y χ g π η τ ρ'
      where
      ρ' : Close (ε - δ) ω (y δ ψ') (rational r)
      ρ' = closeSymmetric (rational r) (y δ ψ') (ε - δ) ω ρ

    κ : (z : (ε : ℚ) → 0 < ε → ℝ) (φ' : CauchyApproximation z)
        (h : (ε : ℚ) → 0 < ε → C) (ψ' : CauchyApproximation'' C D h)
        (r ε δ : ℚ) (ω : 0 < ε) (χ : 0 < δ) (π : 0 < (ε - δ)) →
        (z δ χ) ∼[ ε - δ , π ] (rational r) →
        D (h δ χ) (α r) (ε - δ) π →
        D (β z φ' h ψ') (α r) ε ω
    κ z φ' h ψ' r ε δ ω χ π ρ σ η τ =
      ν r ε δ ω χ π z φ' h ψ' η τ ρ ,
      ο r ε δ ω χ π z φ' h ψ' η τ ρ'
      where
      ρ' : Close (ε - δ) π (rational r) (z δ χ)
      ρ' = closeSymmetric (z δ χ) (rational r) (ε - δ) π ρ

    μ' : (y z : (ε : ℚ) → 0 < ε → ℝ) (g h : (ε : ℚ) → 0 < ε → C)
         (φ' : CauchyApproximation y) (ψ' : CauchyApproximation z)
         (θ' : CauchyApproximation'' C D g)
         (ω : CauchyApproximation'' C D h) (ε δ η : ℚ)
         (χ : 0 < ε) (π : 0 < δ) (ρ : 0 < η) (σ : 0 < (ε - (δ + η))) →
         (y δ π) ∼[ ε - (δ + η) , σ ] (z η ρ) →
         (θ : ℚ) (υ : 0 < θ) →
         Close'LimitLimit y φ' g θ' θ υ →
         Close'LimitLimit z ψ' h ω (θ + ε) (0<+' {x = θ} {y = ε} υ χ)
    μ' y z g h φ' ψ' θ' ω ε δ η χ π ρ σ τ θ υ =
      ∃-rec (close'LimitLimitProposition z ψ' g θ' (θ + ε)
              (0<+' {x = θ} {y = ε} υ χ))
            μ'' 
      where
      μ'' : (ϕζ : ℚ × ℚ) →
            Σ (0 < (fst ϕζ))
            (λ α →
            Σ (0 < (snd ϕζ))
            (λ β →
            Σ (0 < (θ - ((fst ϕζ) + (snd ϕζ))))
            (fst (f (fst ϕζ) α) (y (snd ϕζ) β) (θ - ((fst ϕζ) + (snd ϕζ)))))) →
            Close'LimitLimit z ψ' h ω (θ + ε) (0<+' {x = θ} {y = ε} υ χ)
      μ'' (ϕ , ζ) (α , β , γ , ι) = ∣ (ϕ , η) , (α , ρ , fst ξ' , snd ξ') ∣₁
        where
        κ' : Close (ζ + δ) (0<+' {x = ζ} {y = δ} β π) (y ζ β) (y δ π)
        κ' = φ' ζ δ β π
  
        μ : (u v : ℝ) (ε η : ℚ) (ω : 0 < ε) (θ : 0 < η) →
               Close ε ω u v →
               fst (f ϕ α) u η θ →
               fst (f ϕ α) v (η + ε) (0<+' {x = η} {y = ε} θ ω)
        μ = fst $ snd $ snd $ snd $ f ϕ α

        ν' : fst (f ϕ α) (y δ π) ((θ - (ϕ + ζ)) + (ζ + δ))
                (0<+' {x = θ - (ϕ + ζ)} {y = ζ + δ} γ
                  (0<+' {x = ζ} {y = δ} β π))
        ν' = μ (y ζ β) (y δ π) (ζ + δ) (θ - (ϕ + ζ))
              (0<+' {x = ζ} {y = δ} β π) γ κ' ι

        ν'' : fst (f ϕ α) (z η ρ) ((θ - (ϕ + ζ)) + (ζ + δ) + (ε - (δ + η)))
               (0<+' {x = (θ - (ϕ + ζ)) + (ζ + δ)} {y = (ε - (δ + η))}
                 (0<+' {x = θ - (ϕ + ζ)} {y = ζ + δ} γ
                   (0<+' {x = ζ} {y = δ} β π))
                 σ)
        ν'' = μ (y δ π) (z η ρ) (ε - (δ + η)) ((θ - (ϕ + ζ)) + (ζ + δ)) σ
                    (0<+' {x = θ - (ϕ + ζ)} {y = ζ + δ} γ
                      (0<+' {x = ζ} {y = δ} β π))
                    τ ν'

        ο' : (θ - (ϕ + ζ)) + (ζ + δ) + (ε - (δ + η)) ≡ (θ + ε) - (ϕ + η)
        ο' = ((θ - (ϕ + ζ)) + (ζ + δ)) + (ε - (δ + η))
               ≡⟨ cong (flip _+_ (ε - (δ + η))) (+Assoc (θ - (ϕ + ζ)) ζ δ)  ⟩
             (((θ - (ϕ + ζ)) + ζ) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → (?x + δ) + (ε - (δ + η)))
                       (sym $ +Assoc θ (- (ϕ + ζ)) ζ) ⟩
             ((θ + (- (ϕ + ζ) + ζ)) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → ((θ + (?x + ζ)) + δ) + (ε - (δ + η)))
                       (negateAdd ϕ ζ) ⟩
             ((θ + ((- ϕ + - ζ) + ζ)) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → ((θ + ?x) + δ) + (ε - (δ + η)))
                       (sym $ +Assoc (- ϕ) (- ζ) ζ) ⟩
             ((θ + (- ϕ + (- ζ + ζ))) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → θ + ((- ϕ) + ?x) + δ + (ε - (δ + η))) (+InvL ζ) ⟩
             ((θ + (- ϕ + 0)) + δ) + (ε - (δ + η))
               ≡⟨ cong (λ ?x → θ + ?x + δ + (ε - (δ + η))) (+IdR (- ϕ)) ⟩
             ((θ + - ϕ) + δ) + (ε - (δ + η))
               ≡⟨ (sym $ +Assoc (θ + (- ϕ)) δ (ε - (δ + η))) ⟩
             (θ + - ϕ) + (δ + (ε - (δ + η)))
               ≡⟨ cong (λ ?x → θ + (- ϕ) + (δ + (ε + ?x))) (negateAdd δ η) ⟩
             (θ + - ϕ) + (δ + (ε + ((- δ) + (- η))))
               ≡⟨ cong (_+_ (θ + - ϕ)) (addRightSwap δ ε ((- δ) + (- η))) ⟩
             (θ + - ϕ) + (ε + (δ + ((- δ) + (- η))))
               ≡⟨ cong (λ ?x → θ + (- ϕ) + (ε + ?x)) (+Assoc δ (- δ) (- η)) ⟩
             (θ + - ϕ) + (ε + ((δ + (- δ)) + (- η)))
               ≡⟨ cong (λ ?x → θ + (- ϕ) + (ε + (?x + (- η)))) (+InvR δ) ⟩
             (θ + - ϕ) + (ε + (0 + (- η)))
               ≡⟨ cong (λ ?x → (θ + - ϕ) + (ε + ?x)) (+IdL (- η)) ⟩
             (θ + - ϕ) + (ε + (- η))
               ≡⟨ (sym $ +Assoc θ (- ϕ) (ε + (- η))) ⟩
             θ + (- ϕ + (ε + (- η)))
               ≡⟨ cong (_+_ θ) (addRightSwap (- ϕ) ε (- η)) ⟩
             θ + (ε + ((- ϕ) + (- η)))
               ≡⟨ +Assoc θ ε ((- ϕ) + (- η)) ⟩
             (θ + ε) + ((- ϕ) + (- η))
               ≡⟨ cong (_+_ (θ + ε)) (sym $ negateAdd ϕ η) ⟩
             (θ + ε) - (ϕ + η) ∎
  
        ξ' : Σ (0 < (θ + ε) - (ϕ + η))
               (fst (f ϕ α) (z η ρ) ((θ + ε) - (ϕ + η)))
        ξ' = subst (λ ?x → Σ (0 < ?x) (fst (f ϕ α) (z η ρ) ?x))
                   ο'
                   ((0<+' {x = (θ - (ϕ + ζ)) + (ζ + δ)} {y = ε - (δ + η)}
                     (0<+' {x = θ - (ϕ + ζ)} {y = ζ + δ}
                       γ
                       (0<+' {x = ζ} {y = δ} β π))
                     σ) ,
                    ν'')

    μ : (y z : (ε : ℚ) → 0 < ε → ℝ) (g h : (ε : ℚ) → 0 < ε → C)
        (φ' : CauchyApproximation y) (ψ' : CauchyApproximation z)
        (θ' : CauchyApproximation'' C D g)
        (ω : CauchyApproximation'' C D h) (ε δ η : ℚ)
        (χ : 0 < ε) (π : 0 < δ) (ρ : 0 < η) (σ : 0 < (ε - (δ + η))) →
        (y δ π) ∼[ ε - (δ + η) , σ ] (z η ρ) →
        D (g δ π) (h η ρ) (ε - (δ + η)) σ →
        D (β y φ' g θ') (β z ψ' h ω) ε χ
    μ y z g h φ' ψ' θ' ω ε δ η χ π ρ σ τ υ θ α =
      μ' y z g h φ' ψ' θ' ω ε δ η χ π ρ σ τ θ α ,
      μ' z y h g ψ' φ' ω θ' ε η δ χ ρ π (fst τ') τ'' θ α
      where
      τ' : Σ (0 < ε - (η + δ)) (λ υ → Close (ε - (η + δ)) υ (y δ π) (z η ρ))
      τ' = subst (λ ?x → Σ (0 < ε - ?x)
                           (λ υ → Close (ε - ?x) υ (y δ π) (z η ρ)))
                 (+Comm δ η)
                 (σ , τ)

      τ'' : Close (ε - (η + δ)) (fst τ') (z η ρ) (y δ π)
      τ'' = closeSymmetric (y δ π) (z η ρ) (ε - (η + δ)) (fst τ') (snd τ')

  χ' : (q r ε : ℚ) (φ : 0 < ε)
       (ψ' : - ε < q - r) (ω : q - r < ε)
       (w : ℝ) (η : ℚ) (π : 0 < η) →
       fst (ψ q) w η π →
       fst (ψ r) w (ε + η) (0<+' {x = ε} {y = η} φ π)
  χ' q r ε φ ψ' ω = inductionProposition (ρ , σ , τ)
    where
    ρ : (s η : ℚ) (π : 0 < η) →
        fst (ψ q) (rational s) η π →
        fst (ψ r) (rational s) (ε + η) (0<+' {x = ε} {y = η} φ π)
    ρ s η π ρ' = isTrans≤< ∣ r - s ∣ (∣ r - q ∣ + ∣ q - s ∣) (ε + η)
                           (distanceTriangleInequality r q s)
                           (+<+ {x = ∣ r - q ∣} {y = ε}
                                {z = ∣ q - s ∣} {w = η}
                                σ τ)
      where
      σ : ∣ r - q ∣ < ε
      σ = subst (flip _<_ ε)
                (distanceCommutative q r)
                (<→∣∣< {x = q - r} {ε = ε} ω ψ')

      τ : ∣ q - s ∣ < η
      τ = ρ'

    σ : (x : (ε : ℚ) → 0 < ε → ℝ) (π : CauchyApproximation x)
        (ρ : (ε' : ℚ) (ψ' : 0 < ε') (η : ℚ) (ω : 0 < η) →
             fst (ψ q) (x ε' ψ') η ω →
             fst (ψ r) (x ε' ψ') (ε + η) (0<+' {x = ε} {y = η} φ ω))
        (η : ℚ) (σ : 0 < η) →
        fst (ψ q) (limit x π) η σ →
        fst (ψ r) (limit x π) (ε + η) (0<+' {x = ε} {y = η} φ σ)
    σ x π ρ η σ = ∃-rec isPropPropTrunc τ
      where
      τ : (θ : ℚ) →
          Σ (0 < θ) (λ υ → Σ (0 < η - θ) (λ ι → fst (ψ q) (x θ υ) (η - θ) ι)) →
          fst (ψ r) (limit x π) (ε + η) (0<+' {x = ε} {y = η} φ σ)
      τ θ (υ , α , β) = ∣ θ , (υ , fst ζ , snd ζ) ∣₁
        where
        γ : fst (ψ r) (x θ υ) (ε + (η - θ))
              (0<+' {x = ε} {y = η - θ} φ α)
        γ = ρ θ υ (η - θ) α β 

        ζ : Σ (0 < (ε + η) - θ) (fst (ψ r) (x θ υ) ((ε + η) - θ))
        ζ = subst (λ ?x → Σ (0 < ?x) (fst (ψ r) (x θ υ) ?x))
                  (+Assoc ε η (- θ))
                  ((0<+' {x = ε} {y = η - θ} φ α) , γ)

    τ : (u : ℝ) →
        isProp ((η : ℚ) (π : 0 < η) →
                fst (ψ q) u η π →
                fst (ψ r) u (ε + η) (0<+' {x = ε} {y = η} φ π))
    τ u = isPropΠ3 (λ η π ρ → (fst $ snd $ ψ r) u (ε + η)
                                (0<+' {x = ε} {y = η} φ π))

  χ : (q r ε : ℚ) (φ : 0 < ε) →
      (- ε) < (q - r) → (q - r) < ε →
      B (ψ q) (ψ r) ε φ
  χ q r ε φ ψ ω w η π =
    χ' q r ε φ ψ ω w η π ,
    χ' r q ε φ ω' ψ' w η π
    where
    ω' : - ε < r - q
    ω' = subtract<→negate<subtract q r ε ω

    ψ' : r - q < ε
    ψ' = negate<subtract→subtract< r q ε ψ

  π' : (q ε δ : ℚ) (φ : 0 < ε) (ψ' : 0 < δ) (θ' : 0 < (ε - δ))
       (y : (ε : ℚ) → 0 < ε → ℝ) (ω' : CauchyApproximation y)
       (g : (ε : ℚ) → 0 < ε → A) (χ' : CauchyApproximation'' A B g)
       (π : Close (ε - δ) θ' (rational q) (y δ ψ'))
       (ρ : (u : ℝ) (η : ℚ) (ρ : 0 < η) →
            fst (ψ q) u η ρ →   
            fst (g δ ψ') u ((ε - δ) + η)
              (0<+' {x = ε - δ} {y = η} θ' ρ))
       (η : ℚ) (σ : 0 < η)
       (w : ℝ) →
       fst (ψ q) w η σ →
       fst (ω y ω' g χ') w (ε + η) (0<+' {x = ε} {y = η} φ σ)
  π' q ε δ φ ψ' θ' y ω' g χ' π ρ η σ = inductionProposition (τ , υ , α)
    where
    τ : (r : ℚ) →
        fst (ψ q) (rational r) η σ →
        fst (ω y ω' g χ') (rational r) (ε + η) (0<+' {x = ε} {y = η} φ σ)
    τ r υ = ∣ δ , (ψ' , fst β , snd β) ∣₁
      where
      α : fst (g δ ψ') (rational r) ((ε - δ) + η)
              (0<+' {x = ε - δ} {y = η} θ' σ)
      α = ρ (rational r) η σ υ

      β : Σ (0 < (ε + η) - δ)
            (fst (g δ ψ') (rational r) ((ε + η) - δ))
      β = subst (λ ?x → Σ (0 < ?x) (fst (g δ ψ') (rational r) ?x))
                (addLeftSwap ε (- δ) η)
                ((0<+' {x = ε - δ} {y = η} θ' σ) , α)

    υ : (x : (ε : ℚ) → 0 < ε → ℝ) (α : CauchyApproximation x) →
        ((ε' : ℚ) (β : 0 < ε') →
         fst (ψ q) (x ε' β) η σ →
         fst (ω y ω' g χ') (x ε' β) (ε + η) (0<+' {x = ε} {y = η} φ σ)) →
        fst (ψ q) (limit x α) η σ →
        fst (ω y ω' g χ') (limit x α) (ε + η) (0<+' {x = ε} {y = η} φ σ)
    υ x α β =
      ∃-rec ((fst $ snd $ ω y ω' g χ') (limit x α)
                                       (ε + η)
                                       (0<+' {x = ε} {y = η} φ σ))
            υ'
      where
      υ' : (θ : ℚ) →
           Σ (0 < θ) (λ γ → Σ (0 < η - θ) (fst (ψ q) (x θ γ) (η - θ))) →
           fst (ω y ω' g χ') (limit x α) (ε + η) (0<+' {x = ε} {y = η} φ σ)
      υ' θ (γ , ζ , ι) = ∣ (δ , θ) , (ψ' , γ , fst ν , snd ν) ∣₁
        where
        κ : fst (g δ ψ') (x θ γ) ((ε - δ) + (η - θ))
                (0<+' {x = ε - δ} {y = η - θ} θ' ζ)
        κ = ρ (x θ γ) (η - θ) ζ ι

        μ : (ε - δ) + (η - θ) ≡ (ε + η) - (δ + θ)
        μ = (ε - δ) + (η - θ)
              ≡⟨ (sym $ +Assoc ε (- δ) (η - θ)) ⟩
            ε + (- δ + (η + - θ))
              ≡⟨ cong (_+_ ε) (addRightSwap (- δ) η (- θ) ) ⟩
            ε + (η + (- δ + - θ))
              ≡⟨ cong (λ ?x → ε + (η + ?x)) (sym $ negateAdd δ θ) ⟩
            ε + (η + - (δ + θ))
              ≡⟨ +Assoc ε η (- (δ + θ)) ⟩
            (ε + η) + - (δ + θ) ∎

        ν : Σ (0 < (ε + η) - (δ + θ))
            (fst (g δ ψ') (x θ γ) ((ε + η) - (δ + θ)))
        ν = subst (λ ?x → Σ (0 < ?x) (fst (g δ ψ') (x θ γ) ?x))
                  μ
                  ((0<+' {x = ε - δ} {y = η - θ} θ' ζ) , κ)

    α : (w : ℝ) →
        isProp (fst (ψ q) w η σ → fst (ω y ω' g χ') w (ε + η)
                                      (0<+' {x = ε} {y = η} φ σ))
    α w = isProp→
            ((fst $ snd $ ω y ω' g χ') w
                                       (ε + η)
                                       (0<+' {x = ε} {y = η} φ σ)) 

  ρ' : (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
       (g : (ε : ℚ) → 0 < ε → A) (ψ' : CauchyApproximation'' A B g)
       (r ε δ : ℚ) (θ' : 0 < ε) (ω' : 0 < δ) (χ' : 0 < (ε - δ)) →
       (π : Close (ε - δ) χ' (y δ ω') (rational r))
       (ρ : (u : ℝ) (η : ℚ) (σ : 0 < η) →
            fst (g δ ω') u η σ →
            fst (ψ r) u ((ε - δ) + η) (0<+' {x = ε - δ} {y = η} χ' σ)) →
       (η : ℚ) (σ : 0 < η)
       (w : ℝ) →
       fst (ω y φ g ψ') w η σ →
       fst (ψ r) w (ε + η) (0<+' {x = ε} {y = η} θ' σ)
  ρ' y φ g ψ' r ε δ θ' ω' χ' π ρ η σ = inductionProposition (τ , υ , α)
    where
    τ : (q : ℚ) →
        fst (ω y φ g ψ') (rational q) η σ →
        fst (ψ r) (rational q) (ε + η) (0<+' {x = ε} {y = η} θ' σ)
    τ q = ∃-rec ((fst $ snd $ ψ r) (rational q) (ε + η)
                      (0<+' {x = ε} {y = η} θ' σ))
                τ'
      where
      τ' : (θ : ℚ) →
           Σ (0 < θ)
           (λ υ → Σ (0 < (η - θ)) (fst (g θ υ) (rational q) (η - θ))) →
           fst (ψ r) (rational q) (ε + η) (0<+' {x = ε} {y = η} θ' σ)
      τ' θ (υ , α , β) = snd ι'
        where
        γ : fst (g δ ω') (rational q) (θ + δ + (η - θ))
                  (0<+' {x = θ + δ} {y = η - θ}
                        (0<+' {x = θ} {y = δ} υ ω') α)
        γ = (fst $ ψ' θ δ υ ω' (rational q) (η - θ) α) β

        ζ : θ + δ + (η - θ) ≡ δ + η
        ζ = θ + δ + (η - θ)
              ≡⟨ cong (_+_ (θ + δ)) (+Comm η (- θ)) ⟩
            θ + δ + (- θ + η)
              ≡⟨ +Assoc (θ + δ) (- θ) η ⟩
            ((θ + δ) + - θ) + η
              ≡⟨ cong (flip _+_ η) (addSubtractLeftCancel θ δ) ⟩
            δ + η ∎

        γ' : Σ (0 < δ + η) (fst (g δ ω') (rational q) (δ + η))
        γ' = subst (λ ?x → Σ (0 < ?x) (fst (g δ ω') (rational q) ?x))
                   ζ
                   (0<+' {x = θ + δ} {y = η - θ}
                     (0<+' {x = θ} {y = δ} υ ω') α ,
                    γ)

        ι : fst (ψ r) (rational q) ((ε - δ) + (δ + η))
              (0<+' {x = ε - δ} {y = δ + η} χ' (0<+' {x = δ} {y = η} ω' σ))
        ι = ρ (rational q) (δ + η) (fst γ') (snd γ')

        κ : (ε - δ) + (δ + η) ≡ ε + η
        κ = (ε - δ) + (δ + η)
               ≡⟨ (sym $ +Assoc ε (- δ) (δ + η)) ⟩
            ε + (- δ + (δ + η))
               ≡⟨ cong (_+_ ε) (+Assoc (- δ) δ η) ⟩
            ε + ((- δ + δ) + η)
               ≡⟨ cong (λ ?x → ε + (?x + η)) (+InvL δ) ⟩
            ε + (0 + η)
               ≡⟨ cong (_+_ ε) (+IdL η) ⟩
            ε + η ∎

        ι' : Σ (0 < ε + η) (fst (ψ r) (rational q) (ε + η))
        ι' = subst (λ ?x → Σ (0 < ?x) (fst (ψ r) (rational q) ?x))
                   κ 
                   (0<+' {x = ε - δ} {y = δ + η} χ' (fst γ') , ι)

    υ : (x : (ε : ℚ) → 0 < ε → ℝ) (φ' : CauchyApproximation x) →
        ((ε' : ℚ) (ψ'' : 0 < ε') →
         fst (ω y φ g ψ') (x ε' ψ'') η σ →
         fst (ψ r) (x ε' ψ'') (ε + η) (0<+' {x = ε} {y = η} θ' σ)) →
        fst (ω y φ g ψ') (limit x φ') η σ →
        fst (ψ r) (limit x φ') (ε + η) (0<+' {x = ε} {y = η} θ' σ)
    υ x φ' τ =
      ∃-rec
        ((fst $ snd $ ψ r) (limit x φ') (ε + η)
          (0<+' {x = ε} {y = η}  θ' σ))
        υ'
      where
      υ' : (θζ : ℚ × ℚ) →
            Σ (0 < fst θζ)
            (λ α →
            Σ (0 < snd θζ)
            (λ β →
            Σ (0 < η - ((fst θζ) + (snd θζ)))
            (fst (g (fst θζ) α) (x (snd θζ) β) (η - ((fst θζ) + (snd θζ)))))) →
            fst (ψ r) (limit x φ') (ε + η) (0<+' {x = ε} {y = η} θ' σ)
      υ' (θ , ζ) (α , β , γ , ι) = ∣ ζ , (β , fst ν' , snd ν') ∣₁
        where
        κ : fst (g δ ω') (x ζ β) (θ + δ + (η - (θ + ζ)))
                (0<+' {x = θ + δ} {y = η - (θ + ζ)}
                  (0<+' {x = θ} {y = δ} α ω') γ)
        κ = (fst $ ψ' θ δ α ω' (x ζ β) (η - (θ + ζ)) γ) ι

        μ : θ + δ + (η - (θ + ζ)) ≡ δ + (η - ζ)
        μ = θ + δ + (η - (θ + ζ))
              ≡⟨ cong (λ ?x → (θ + δ) + (η + ?x)) (negateAdd θ ζ) ⟩
            θ + δ + (η + (- θ + - ζ))
              ≡⟨ cong (_+_ (θ + δ)) (addRightSwap η (- θ) (- ζ)) ⟩
            θ + δ + (- θ + (η + - ζ))
              ≡⟨ +Assoc (θ + δ) (- θ) (η + (- ζ)) ⟩
            ((θ + δ) + - θ) + (η + - ζ)
              ≡⟨ cong (flip _+_ (η + - ζ)) (addSubtractLeftCancel θ δ) ⟩
            δ + (η + - ζ) ∎

        κ' : Σ (0 < δ + η - ζ)
                 (fst (g δ ω') (x ζ β) (δ + η - ζ))
        κ' = subst (λ ?x → Σ (0 < ?x) (fst (g δ ω') (x ζ β) ?x))
                     μ
                     ((0<+' {x = θ + δ} {y = η - (θ + ζ)}
                        (0<+' {x = θ} {y = δ} α ω') γ) ,
                      κ)

        ξ : (ε - δ) + (δ + (η - ζ)) ≡ ((ε + η) - ζ)
        ξ = (ε - δ) + (δ + (η - ζ))
              ≡⟨ +Assoc (ε - δ) δ (η - ζ) ⟩
            ((ε - δ) + δ) + (η - ζ)
              ≡⟨ cong (flip _+_ (η - ζ)) (subtractAddRightCancel δ ε) ⟩
            ε + (η - ζ)
              ≡⟨ +Assoc ε η (- ζ) ⟩
            (ε + η) - ζ ∎

        ν : fst (ψ r) (x ζ β) ((ε - δ) + (δ + (η - ζ)))
                (0<+' {x = ε - δ} {y = δ + (η - ζ)} χ' (fst κ'))
        ν = ρ (x ζ β) (δ + (η - ζ)) (fst κ') (snd κ')

        ν' : Σ (0 < (ε + η) - ζ)
                 (fst (ψ r) (x ζ β) ((ε + η) - ζ))
        ν' = subst (λ ?x → Σ (0 < ?x) (fst (ψ r) (x ζ β) ?x))
                     ξ
                     (0<+' {x = ε - δ} {y = δ + (η - ζ)} χ' (fst κ') ,
                      ν)

    α : (u : ℝ) →
        isProp (fst (ω y φ g ψ') u η σ → fst (ψ r) u (ε + η)
                 (0<+' {x = ε} {y = η} θ' σ))
    α u = isProp→ ((fst $ snd $ ψ r) u (ε + η) (0<+' {x = ε} {y = η} θ' σ))

  π : (q ε δ : ℚ) (φ : 0 < ε) (ψ' : 0 < δ) (θ' : 0 < (ε - δ))
      (y : (ε : ℚ) → 0 < ε → ℝ) (ω' : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → A) (χ' : CauchyApproximation'' A B g) →
      Close (ε - δ) θ' (rational q) (y δ ψ') →
      B (ψ q) (g δ ψ') (ε - δ) θ' →
      B (ψ q) (ω y ω' g χ') ε φ
  π q ε δ φ ψ' θ y ω' g χ' π ρ w η σ =
    π' q ε δ φ ψ' θ y ω' g χ' π ρ'' η σ w ,
    ρ' y ω' g χ' q ε δ φ ψ' θ π'' ρ''' η σ w
    where
    ρ'' : (u : ℝ) (η : ℚ) (ρ : 0 < η) →
          fst (ψ q) u η ρ →
          fst (g δ ψ') u ((ε - δ) + η) (0<+' {x = ε - δ} {y = η} θ ρ)
    ρ'' u η ρ' = fst $ ρ u η ρ'

    ρ''' : (u : ℝ) (η : ℚ) (ρ : 0 < η) →
           fst (g δ ψ') u η ρ →
           fst (ψ q) u ((ε - δ) + η) (0<+' {x = ε - δ} {y = η} θ ρ)
    ρ''' u η ρ' = snd $ ρ u η ρ'

    π'' : Close (ε - δ) θ (y δ ψ') (rational q)
    π'' = closeSymmetric (rational q) (y δ ψ') (ε - δ) θ π

  ρ : (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
      (g : (ε : ℚ) → 0 < ε → A) (ψ' : CauchyApproximation'' A B g)
      (r ε δ : ℚ) (θ' : 0 < ε) (ω' : 0 < δ) (χ' : 0 < (ε - δ)) →
      Close (ε - δ) χ' (y δ ω') (rational r) →
      B (g δ ω') (ψ r) (ε - δ) χ' →
      B (ω y φ g ψ') (ψ r) ε θ'
  ρ y φ g ψ' r ε δ θ' ω' χ' π ρ w η σ =
    ρ' y φ g ψ' r ε δ θ' ω' χ' π ρ''' η σ w ,
    π' r ε δ θ' ω' χ' y φ g ψ' π'' ρ'' η σ w
    where
    π'' : Close (ε - δ) χ' (rational r) (y δ ω')
    π'' = closeSymmetric (y δ ω') (rational r) (ε - δ) χ' π

    ρ'' : (u : ℝ) (η : ℚ) (ρ' : 0 < η) →
         fst (ψ r) u η ρ' →
         fst (g δ ω') u ((ε - δ) + η) (0<+' {x = ε - δ} {y = η} χ' ρ')
    ρ'' u η ρ' = snd $ ρ u η ρ'

    ρ''' : (u : ℝ) (η : ℚ) (ρ : 0 < η) →
           fst (g δ ω') u η ρ →
           fst (ψ r) u ((ε - δ) + η) (0<+' {x = ε - δ} {y = η} χ' ρ)
    ρ''' u η ρ' = fst $ ρ u η ρ'

  σ' : (x y : (ε : ℚ) → 0 < ε → ℝ) (f g : (ε : ℚ) → 0 < ε → A)
       (φ : CauchyApproximation x) (ψ' : CauchyApproximation y)
       (θ' : CauchyApproximation'' A B f)
       (ω' : CauchyApproximation'' A B g) (ε δ η : ℚ) (χ' : 0 < ε)
       (π' : 0 < δ) (ρ' : 0 < η) (σ : 0 < (ε - (δ + η)))
       (τ : Close (ε - (δ + η)) σ (x δ π') (y η ρ'))
       (υ : (w : ℝ) (θ : ℚ) (α : 0 < θ) →
            (fst (f δ π') w θ α) →
            (fst (g η ρ') w ((ε - (δ + η)) + θ)
              (0<+' {x = ε - (δ + η)} {y = θ} σ α)))
       (θ : ℚ) (υ : 0 < θ)
       (w : ℝ) →
       fst (ω x φ f θ') w θ υ →
       fst (ω y ψ' g ω') w (ε + θ) (0<+' {x = ε} {y = θ} χ' υ)
  σ' x y f g φ ψ' θ' ω' ε δ η χ' π' ρ' σ τ υ θ α =
    inductionProposition (β , γ , ζ)
    where
    β : (q : ℚ) →
        fst (ω x φ f θ') (rational q) θ α →
        fst (ω y ψ' g ω') (rational q) (ε + θ) (0<+' {x = ε} {y = θ} χ' α)
    β q =
      ∃-rec ((fst $ snd $ ω y ψ' g ω') (rational q) (ε + θ)
                  (0<+' {x = ε} {y = θ} χ' α))
            β'
      where
      β' : (ϕ : ℚ) →
           Σ (0 < ϕ)
           (λ γ → Σ (0 < (θ - ϕ)) (fst (f ϕ γ) (rational q) (θ - ϕ))) →
           fst (ω y ψ' g ω') (rational q) (ε + θ) (0<+' {x = ε} {y = θ} χ' α)
      β' ϕ (γ , ι , κ) = ∣ η , (ρ' , fst ξ' , snd ξ') ∣₁
        where
        μ : fst (f δ π') (rational q) (ϕ + δ + (θ - ϕ))
                (0<+' {x = ϕ + δ} {y = θ - ϕ} (0<+' {x = ϕ} {y = δ} γ π') ι)
        μ = (fst $ θ' ϕ δ γ π' (rational q) (θ - ϕ) ι) κ

        ν : ϕ + δ + (θ - ϕ) ≡ δ + θ
        ν = ϕ + δ + (θ - ϕ)
              ≡⟨ cong (_+_ (ϕ + δ)) (+Comm θ (- ϕ)) ⟩
            ϕ + δ + (- ϕ + θ)
              ≡⟨ +Assoc (ϕ + δ) (- ϕ) θ ⟩
            ((ϕ + δ) + - ϕ) + θ
              ≡⟨ cong (flip _+_ θ) (addSubtractLeftCancel ϕ δ) ⟩
            δ + θ ∎

        μ' : Σ (0 < δ + θ) (fst (f δ π') (rational q) (δ + θ))
        μ' = subst (λ ?x → Σ (0 < ?x) (fst (f δ π') (rational q) ?x))
                   ν
                   ((0<+' {x = ϕ + δ} {y = θ - ϕ}
                     (0<+' {x = ϕ} {y = δ} γ π') ι) ,
                    μ)

        ξ : fst (g η ρ') (rational q) ((ε - (δ + η)) + (δ + θ))
                (0<+' {x = ε - (δ + η)} {y = δ + θ} σ (fst μ'))
        ξ = υ (rational q) (δ + θ) (fst μ') (snd μ')

        ο : (ε - (δ + η)) + (δ + θ) ≡ ((ε + θ) - η)
        ο = (ε - (δ + η)) + (δ + θ)
              ≡⟨ cong (λ ?x → (ε + ?x) + (δ + θ)) (negateAdd δ η) ⟩
            (ε + (- δ + - η)) + (δ + θ)
              ≡⟨ (sym $ +Assoc ε (- δ + - η) (δ + θ)) ⟩
            ε + ((- δ + - η) + (δ + θ))
              ≡⟨ cong (λ ?x → ε + (?x + (δ + θ))) (+Comm (- δ) (- η)) ⟩
            ε + ((- η + - δ) + (δ + θ))
              ≡⟨ cong (_+_ ε) (sym $ +Assoc (- η) (- δ) (δ + θ) ) ⟩
            ε + (- η + (- δ + (δ + θ)))
              ≡⟨ cong (λ ?x → ε + (- η + ?x)) (+Assoc (- δ) δ θ) ⟩
            ε + (- η + ((- δ + δ) + θ))
              ≡⟨ cong (λ ?x → ε + (- η + (?x + θ))) (+InvL δ) ⟩
            ε + (- η + (0 + θ))
              ≡⟨ cong (λ ?x → ε + (- η + ?x)) (+IdL θ) ⟩
            ε + (- η + θ)
              ≡⟨ cong (_+_ ε) (+Comm (- η) θ) ⟩
            ε + (θ + - η)
              ≡⟨ +Assoc ε θ (- η) ⟩
            (ε + θ) + - η ∎

        ξ' : Σ (0 < (ε + θ) - η)
               (fst (g η ρ') (rational q) ((ε + θ) - η))
        ξ' = subst (λ ?x → Σ (0 < ?x) (fst (g η ρ') (rational q) ?x))
                   ο
                   (0<+' {x = ε - (δ + η)} {y = δ + θ} σ (fst μ') , ξ)

    γ : (z : (ε : ℚ) → 0 < ε → ℝ) (φ' : CauchyApproximation z) →
        ((ε' : ℚ) (ψ'' : 0 < ε') →
         fst (ω x φ f θ') (z ε' ψ'') θ α →
         fst (ω y ψ' g ω') (z ε' ψ'') (ε + θ) (0<+' {x = ε} {y = θ} χ' α)) →
        fst (ω x φ f θ') (limit z φ') θ α →
        fst (ω y ψ' g ω') (limit z φ') (ε + θ) (0<+' {x = ε} {y = θ} χ' α)
    γ z φ' ι =
      ∃-rec ((fst $ snd (ω y ψ' g ω')) (limit z φ') (ε + θ)
               (0<+' {x = ε} {y = θ} χ' α))
            γ'
      where
      γ' : (ϕζ : ℚ × ℚ) →
           Σ (0 < fst ϕζ)
           (λ κ →
           Σ (0 < snd ϕζ)
           (λ μ →
           Σ (0 < θ - (fst ϕζ + snd ϕζ))
           (fst (f (fst ϕζ) κ) (z (snd ϕζ) μ) (θ - (fst ϕζ + snd ϕζ))))) →
           fst (ω y ψ' g ω') (limit z φ') (ε + θ) (0<+' {x = ε} {y = θ} χ' α)
      γ' (ϕ , ζ) (κ , μ , ν , ξ) = ∣ (η , ζ) , (ρ' , μ , fst r' , snd r') ∣₁
        where
        p : fst (f δ π') (z ζ μ) (ϕ + δ + (θ - (ϕ + ζ)))
                (0<+' {x = ϕ + δ} {y = θ - (ϕ + ζ)}
                  (0<+' {x = ϕ} {y = δ} κ π') ν)
        p = (fst $ θ' ϕ δ κ π' (z ζ μ) (θ - (ϕ + ζ)) ν) ξ

        q : ϕ + δ + (θ - (ϕ + ζ)) ≡ (δ + θ) - ζ
        q = ϕ + δ + (θ - (ϕ + ζ))
              ≡⟨ cong (λ ?x → (ϕ + δ) + (θ + ?x)) (negateAdd ϕ ζ) ⟩
            ϕ + δ + (θ + (- ϕ + - ζ))
              ≡⟨ cong (_+_ (ϕ + δ)) (addRightSwap θ (- ϕ) (- ζ)) ⟩
            ϕ + δ + (- ϕ + (θ + - ζ))
              ≡⟨ +Assoc (ϕ + δ) (- ϕ) (θ + - ζ) ⟩
            ((ϕ + δ) + - ϕ) + (θ + - ζ)
              ≡⟨ cong (flip _+_ (θ + - ζ)) (addSubtractLeftCancel ϕ δ) ⟩
            δ + (θ + - ζ)
              ≡⟨ +Assoc δ θ (- ζ) ⟩
            (δ + θ) + - ζ ∎

        p' : Σ (0 < (δ + θ) - ζ) 
                 (fst (f δ π') (z ζ μ) ((δ + θ) - ζ))
        p' = subst (λ ?x → Σ (0 < ?x) (fst (f δ π') (z ζ μ) ?x))
                     q
                     ((0<+' {x = ϕ + δ} {y = θ - (ϕ + ζ)}
                        (0<+' {x = ϕ} {y = δ} κ π') ν),
                      p)

        r : fst (g η ρ') (z ζ μ) ((ε - (δ + η)) + ((δ + θ) - ζ))
                (0<+' {x = ε - (δ + η)} {y = (δ + θ) - ζ} σ (fst p'))
        r = υ (z ζ μ) ((δ + θ) - ζ) (fst p') (snd p')

        s : (ε - (δ + η)) + ((δ + θ) - ζ) ≡ ((ε + θ) - (η + ζ))
        s = (ε - (δ + η)) + ((δ + θ) - ζ)
              ≡⟨ cong (λ ?x → (ε + ?x) + ((δ + θ) - ζ)) (negateAdd δ η) ⟩
            (ε + (- δ + - η)) + ((δ + θ) - ζ)
              ≡⟨ (sym $ +Assoc ε (- δ + - η) ((δ + θ) - ζ) ) ⟩
            ε + ((- δ + - η) + ((δ + θ) - ζ))
              ≡⟨ cong (_+_ ε) (+Assoc (- δ + - η) (δ + θ) (- ζ)) ⟩
            ε + (((- δ + - η) + (δ + θ)) - ζ)
              ≡⟨ cong (λ ?x → ε + (?x - ζ)) (+Assoc (- δ + - η) δ θ) ⟩
            ε + ((((- δ + - η) + δ) + θ) - ζ)
              ≡⟨ cong (λ ?x → ε + ((?x + θ) - ζ)) (addLeftSwap (- δ) (- η) δ) ⟩
            ε + ((((- δ + δ) + - η) + θ) - ζ)
              ≡⟨ cong (λ ?x → ε + (((?x + - η) + θ) - ζ)) (+InvL δ) ⟩
            ε + (((0 + - η) + θ) - ζ)
              ≡⟨ cong (λ ?x → ε + ((?x + θ) - ζ)) (+IdL (- η)) ⟩
            ε + ((- η + θ) - ζ)
              ≡⟨ cong (λ ?x → ε + (?x - ζ)) (+Comm (- η) θ) ⟩
            ε + ((θ + - η) - ζ)
              ≡⟨ cong (_+_ ε) (sym $ +Assoc θ (- η) (- ζ)) ⟩
            ε + (θ + (- η + - ζ))
              ≡⟨ +Assoc ε θ ((- η) + (- ζ)) ⟩
            (ε + θ) + (- η + - ζ)
              ≡⟨ cong (_+_ (ε + θ)) (sym $ negateAdd η ζ) ⟩
            (ε + θ) - (η + ζ) ∎

        r' : Σ (0 < (ε + θ) - (η + ζ))
                 (fst (g η ρ') (z ζ μ) ((ε + θ) - (η + ζ)))
        r' = subst (λ ?x → Σ (0 < ?x) (fst (g η ρ') (z ζ μ) ?x))
                     s
                     (((0<+' {x = ε - (δ + η)} {y = (δ + θ) - ζ}
                          σ (fst p'))) ,
                      r)

    ζ : (u : ℝ) →
        isProp (fst (ω x φ f θ') u θ α → fst (ω y ψ' g ω') u (ε + θ)
                    (0<+' {x = ε} {y = θ} χ' α))
    ζ u = isProp→ ((fst $ snd $ ω y ψ' g ω') u (ε + θ)
                        (0<+' {x = ε} {y = θ} χ' α))

  σ : (x y : (ε : ℚ) → 0 < ε → ℝ) (f g : (ε : ℚ) → 0 < ε → A)
      (φ : CauchyApproximation x) (ψ' : CauchyApproximation y)
      (θ' : CauchyApproximation'' A B f)
      (ω' : CauchyApproximation'' A B g) (ε δ η : ℚ) (χ' : 0 < ε)
      (π' : 0 < δ) (ρ' : 0 < η) (σ : 0 < (ε - (δ + η)))
      (τ : Close (ε - (δ + η)) σ (x δ π') (y η ρ')) →
      B (f δ π') (g η ρ') (ε - (δ + η)) σ →
      B (ω x φ f θ') (ω y ψ' g ω') ε χ'
  σ x y f g φ ψ' θ' ω' ε δ η χ' π' ρ' σ τ υ w θ α =
    σ' x y f g φ ψ' θ' ω' ε δ η χ' π' ρ' σ τ υ'' θ α w ,
    σ' y x g f ψ' φ ω' θ' ε η δ χ' ρ' π' (fst τ') τ'' υ''' θ α w
    where
    υ'' : (w : ℝ) (θ : ℚ)
          (α : 0 < θ) →
          fst (f δ π') w θ α →
          fst (g η ρ') w ((ε - (δ + η)) + θ)
            (0<+' {x = ε - (δ + η)} {y = θ} σ α)
    υ'' w θ α = fst $ υ w θ α

    τ' : Σ (0 < ε - (η + δ)) (λ β → Close (ε - (η + δ)) β (x δ π') (y η ρ'))
    τ' = subst (λ ?x → Σ (0 < ε - ?x)
                         (λ β → Close (ε - ?x) β (x δ π') (y η ρ')))
               (+Comm δ η)
               (σ , τ) 

    τ'' : Close (ε - (η + δ)) (fst τ') (y η ρ') (x δ π')
    τ'' = closeSymmetric (x δ π') (y η ρ') (ε - (η + δ)) (fst τ') (snd τ')

    υ''' : (w : ℝ) (θ : ℚ)
           (α : 0 < θ) →
           fst (g η ρ') w θ α →
           fst (f δ π') w ((ε - (η + δ)) + θ)
             (0<+' {x = ε - (η + δ)} {y = θ} (fst τ') α)
    υ''' w θ α β = ζ'
      where
      γ : fst (f δ π') w ((ε - (δ + η)) + θ)
          (0<+' {x = ε - (δ + η)} {y = θ} σ α)
      γ = (snd $ υ w θ α) β

      ζ : Σ (0 < (ε - (η + δ)) + θ)
            (fst (f δ π') w ((ε - (η + δ)) + θ))
      ζ = subst (λ ?x → Σ (0 < ?x) (fst (f δ π') w ?x))
                (cong (λ ?x → (ε - ?x) + θ) (+Comm δ η))
                (0<+' {x = ε - (δ + η)} {y = θ} σ α , γ)

      ζ' : fst (f δ π') w ((ε - (η + δ)) + θ)
               (0<+' {x = ε - (η + δ)} {y = θ} (fst τ') α)
      ζ' = subst (fst (f δ π') w ((ε - (η + δ)) + θ))
                 (isProp< 0 ((ε - (η + δ)) + θ)
                          (fst ζ) (0<+' {x = ε - (η + δ)} {y = θ} (fst τ') α))
                 (snd ζ)
