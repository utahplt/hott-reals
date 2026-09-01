module HoTTReals.Data.Real.Nonexpanding where

import Cubical.Data.Bool as Bool
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Binary.Order.QuosetReasoning
open import Cubical.Relation.Nullary

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

nonexpandingℚ→lipschitzℚ :
  (f : ℚ → ℚ) →
  Nonexpandingℚ f → Lipschitzℚ (rational ∘ f) 1 0<1
nonexpandingℚ→lipschitzℚ f φ q r ε ψ ω = π'
  where
  χ : ∣ f q - f r ∣ < ε
  χ = isTrans≤< ∣ f q - f r ∣ ∣ q - r ∣ ε (φ q r) ω

  χ' : Close ε ψ (rational (f q)) (rational (f r))
  χ' = rationalRational
         (f q) (f r)
         ε ψ
         (∣∣<→<₂ {x = f q - f r} {ε = ε} χ)
         (∣∣<→<₁ {x = f q - f r} {ε = ε} χ)

  π : Σ (0 < 1 · ε) (λ ξ → Close (1 · ε) ξ (rational (f q)) (rational (f r)))
  π = subst (λ ?x → Σ (0 < ?x)
                      (λ ξ → Close ?x ξ (rational (f q)) (rational (f r))))
            (sym $ ·IdL ε)
            (ψ , χ')

  π' : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ)
             (rational (f q)) (rational (f r))
  π' = subst (λ ?ξ → Close (1 · ε) ?ξ (rational (f q)) (rational (f r)))
             (isProp< 0 (1 · ε) (fst π) (0<· {x = 1} {y = ε} 0<1 ψ))
             (snd π)

-- TODO: lipschitz → nonexpanding for rationals kind of difficult

nonexpandingℝ→lipschitzℝ :
  (f : ℝ → ℝ) →
  Nonexpandingℝ f → Lipschitzℝ f 1 0<1
nonexpandingℝ→lipschitzℝ f φ u v ε ψ ω = π'
  where
  χ : Close ε ψ (f u) (f v)
  χ = φ u v ε ψ ω

  π : Σ (0 < 1 · ε) (λ ξ → Close (1 · ε) ξ (f u) (f v))
  π = subst (λ ?x → Σ (0 < ?x) (λ ξ → Close ?x ξ (f u) (f v)))
            (sym $ ·IdL ε)
            (ψ , χ)

  π' : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ) (f u) (f v)
  π' = subst (λ ?ξ → Close (1 · ε) ?ξ (f u) (f v))
             (isProp< 0 (1 · ε) (fst π) (0<· {x = 1} {y = ε} 0<1 ψ))
             (snd π)

lipschitzℝ→nonexpandingℝ :
  (f : ℝ → ℝ) →
  Lipschitzℝ f 1 0<1 → Nonexpandingℝ f
lipschitzℝ→nonexpandingℝ f φ u v ε ψ ω = π'
  where
  χ : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ) (f u) (f v)
  χ = φ u v ε ψ ω

  π : Σ (0 < ε) (λ ξ → Close ε ξ (f u) (f v))
  π = subst (λ ?x → Σ (0 < ?x) (λ ξ → Close ?x ξ (f u) (f v)))
            (·IdL ε)
            ((0<· {x = 1} {y = ε} 0<1 ψ) , χ)

  π' : Close ε ψ (f u) (f v)
  π' = subst (λ ?ξ → Close ε ?ξ (f u) (f v))
             (isProp< 0 ε (fst π) ψ)
             (snd π)

nonexpandingℚ₂→lipschitzℚ₂ :
  (f : ℚ → ℚ → ℚ)
  (φ : Nonexpandingℚ₂ f)
  (q : ℚ) → Lipschitzℚ (rational ∘ f q) 1 0<1 
nonexpandingℚ₂→lipschitzℚ₂ f φ q r s ε ψ ω =
  rationalRational
    (f q r) (f q s)
    (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ)
    (∣∣<→<₂ {x = f q r - f q s} {ε = 1 · ε} π)
    (∣∣<→<₁ {x = f q r - f q s} {ε = 1 · ε} π)
  where
  ω' : ∣ r - s ∣ < 1 · ε
  ω' = subst (_<_ ∣ r - s ∣) (sym $ ·IdL ε) ω

  χ : ∣ f q r - f q s ∣ ≤ ∣ r - s ∣
  χ = snd φ q r s

  π : ∣ f q r - f q s ∣ < 1 · ε
  π = isTrans≤< ∣ f q r - f q s ∣ ∣ r - s ∣ (1 · ε) χ ω'

nonexpandingℚ₂→lipschitzℚ₁ :
  (f : ℚ → ℚ → ℚ) →
  (φ : Nonexpandingℚ₂ f) →
  (r : ℚ) → Lipschitzℚ (rational ∘ flip f r) 1 0<1 
nonexpandingℚ₂→lipschitzℚ₁ f φ r q s ε ψ ω =
  rationalRational
    (flip f r q) (flip f r s)
    (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ)
    (∣∣<→<₂ {x = f q r - f s r} {ε = 1 · ε} π)
    (∣∣<→<₁ {x = f q r - f s r} {ε = 1 · ε} π)
  where
  ω' : ∣ q - s ∣ < 1 · ε
  ω' = subst (_<_ ∣ q - s ∣) (sym $ ·IdL ε) ω

  χ : ∣ f q r - f s r ∣ ≤ ∣ q - s ∣
  χ = fst φ r q s

  π : ∣ f q r - f s r ∣ < 1 · ε
  π = isTrans≤< ∣ f q r - f s r ∣ ∣ q - s ∣ (1 · ε) χ ω'

nonexpandingℝ₂→lipschitzℝ₂ : 
  (f : ℝ → ℝ → ℝ) →
  (φ : Nonexpandingℝ₂ f) →
  (u : ℝ) → Lipschitzℝ (f u) 1 0<1 
nonexpandingℝ₂→lipschitzℝ₂ f φ u v w ε ψ ω = ρ
  where
  χ : Close ε ψ (f u v) (f u w)
  χ = snd φ u v w ε ψ ω

  π : Σ (0 < 1 · ε) (λ ρ → Close (1 · ε) ρ (f u v) (f u w))
  π = subst (λ ?x → Σ (0 < ?x) (λ ρ → Close ?x ρ _ _)) (sym $ ·IdL ε) (ψ , χ)

  ρ : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ) (f u v) (f u w)
  ρ = subst (λ ?x → Close (1 · ε) ?x (f u v) (f u w))
            (isProp< 0 (1 · ε) (fst π) (0<· {x = 1} {y = ε} 0<1 ψ))
            (snd π)

nonexpandingℝ₂→lipschitzℝ₁ : 
  (f : ℝ → ℝ → ℝ) →
  (φ : Nonexpandingℝ₂ f) →
  (w : ℝ) → Lipschitzℝ (flip f w) 1 0<1 
nonexpandingℝ₂→lipschitzℝ₁ f φ w u v ε ψ ω =
  ρ
  where
  χ : Close ε ψ (f u w) (f v w)
  χ = fst φ w u v ε ψ ω

  π : Σ (0 < 1 · ε) (λ ρ → Close (1 · ε) ρ (f u w) (f v w))
  π = subst (λ ?x → Σ (0 < ?x) (λ ρ → Close ?x ρ _ _)) (sym $ ·IdL ε) (ψ , χ)

  ρ : Close (1 · ε) (0<· {x = 1} {y = ε} 0<1 ψ) (f u w) (f v w)
  ρ = subst (λ ?x → Close (1 · ε) ?x (f u w) (f v w))
            (isProp< 0 (1 · ε) (fst π) (0<· {x = 1} {y = ε} 0<1 ψ))
            (snd π)

liftNonexpanding₂Type : Type
liftNonexpanding₂Type =
  Σ (ℝ → ℝ)
    (λ h → (ε : ℚ) (φ : 0 < ε) (u v : ℝ) → u ∼[ ε , φ ] v → h u ∼[ ε , φ ] h v)

liftNonexpanding₂Relation :
  liftNonexpanding₂Type → liftNonexpanding₂Type → (ε : ℚ) → 0 < ε → Type
liftNonexpanding₂Relation (h , _) (g , _) ε φ = (u : ℝ) → h u ∼[ ε , φ ] g u

liftNonexpanding₂Recursion : 
  (f : ℚ → ℚ → ℚ) →
  Nonexpandingℚ₂ f →
  Recursion liftNonexpanding₂Type liftNonexpanding₂Relation
liftNonexpanding₂Recursion f (φ , ψ) =
  -- Gotta go, gotta go, more pies to bake up
  rationalCase ,
  limitCase ,
  seperated ,
  rationalRationalCase ,
  rationalLimitCase ,
  limitRationalCase ,
  limitLimitCase ,
  relation
  where
  rationalCase : ℚ → liftNonexpanding₂Type
  rationalCase q =
    fRational , π'
    where
    ω : 0 < 1
    ω = Bool.toWitness {Q = <Dec 0 1} tt

    χ : Lipschitzℚ (rational ∘ (f q)) 1 ω
    χ r s ε π ρ = nonexpandingℚ₂→lipschitzℚ₂ f (φ , ψ) q r s ε π ρ

    fRational : ℝ → ℝ
    fRational = liftLipschitz (rational ∘ (f q)) 1 ω χ

    π' : (ε : ℚ) (ρ : 0 < ε) (u v : ℝ) →
         Close ε ρ u v →
         Close ε ρ (fRational u) (fRational v)
    π' ε ρ u v σ =
      τ''
      where
      -- Doesn't like to be typed for some reason, Agda lags out during type
      -- checking
      τ = liftLipschitzLipschitz (rational ∘ (f q)) 1 ω χ u v ε ρ σ
                                                                  
      τ' : Σ (0 < ε) (λ ρ' → Close ε ρ' (fRational u) (fRational v))
      τ' = subst (λ ?x → Σ (0 < ?x)
                           (λ ρ' → Close ?x ρ' (fRational u) (fRational v)))
                 (·IdL ε)
                 ((0<· {x = 1} {y = ε} ω ρ) , τ)
           
      τ'' : Close ε ρ (fRational u) (fRational v)
      τ'' = subst (λ ?x → Close ε ?x _ _) (isProp< 0 ε (fst τ') ρ) (snd τ')

  fLimit' :
    (f : (ε : ℚ) → 0 < ε → liftNonexpanding₂Type) →
    ℝ → (ε : ℚ) → 0 < ε → ℝ
  fLimit' f v ε π = fst (f ε π) v

  fLimit'-cauchy :
    (f : (ε : ℚ) → 0 < ε → liftNonexpanding₂Type)
    (v : ℝ) →
    CauchyApproximation'' liftNonexpanding₂Type liftNonexpanding₂Relation f →
    CauchyApproximation $ fLimit' f v
  fLimit'-cauchy f v χ ε δ ρ σ = χ ε δ ρ σ v

  limitCase :
    (x : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation x)
    (f : (ε : ℚ) → 0 < ε → liftNonexpanding₂Type) →
    CauchyApproximation'' liftNonexpanding₂Type liftNonexpanding₂Relation f →
    liftNonexpanding₂Type
  limitCase x ω f χ = fLimit , ρ
    where
    -- π : (v : ℝ) → CauchyApproximation $ fLimit' f v
    -- π v ε δ ρ σ = χ ε δ ρ σ v

    fLimit : ℝ → ℝ
    fLimit v = limit (fLimit' f v) (fLimit'-cauchy f v χ)

    ρ : (ε : ℚ) (σ : 0 < ε) (u v : ℝ) →
        Close ε σ u v →
        Close ε σ (fLimit u) (fLimit v)
    ρ ε σ u v τ =
      ∃-rec (squash ε σ (fLimit u) (fLimit v)) ρ' (closeOpen u v ε σ τ)
      where
      ρ' : (θ : ℚ) →
           (0 < θ) × Σ (0 < (ε - θ)) (λ υ → Close (ε - θ) υ u v) →
           Close ε σ (fLimit u) (fLimit v)
      ρ' θ (υ , ξ , ο) =
        limitLimit
          (fLimit' f u) (fLimit' f v)
          (fLimit'-cauchy f u χ) (fLimit'-cauchy f v χ)
          ε (θ / 2 [ α' ]) (θ / 2 [ α' ])
          σ α'' α''
          (fst β')
          (snd β')
        where
        α : 0 < 2
        α = Bool.toWitness {Q = <Dec 0 2} tt

        α' : ¬ 2 ≡ 0
        α' = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt

        α'' : 0 < θ / 2 [ α' ]
        α'' = 0</' {x = θ} {y = 2} υ α

        β : Close (ε - θ) ξ
                  (fLimit' f u (θ / 2 [ α' ]) α'')
                  (fLimit' f v (θ / 2 [ α' ]) α'')
        β = (snd $ f (θ / 2 [ α' ]) α'')
              (ε - θ) ξ u v ο

        γ : (θ / 2 [ α' ]) + (θ / 2 [ α' ]) ≡ θ
        γ = self/2≡self θ α'

        β' : Σ (0 < ε - ((θ / 2 [ α' ]) + (θ / 2 [ α' ])))
               (λ ξ → Close (ε - ((θ / 2 [ α' ]) + (θ / 2 [ α' ]))) ξ
                            (fLimit' f u (θ / 2 [ α' ]) α'')
                            (fLimit' f v (θ / 2 [ α' ]) α''))
        β' = subst
                 (λ ?x → Σ (0 < ?x)
                   (λ ξ → Close ?x ξ
                            (fLimit' f u (θ / 2 [ α' ]) α'')
                            (fLimit' f v (θ / 2 [ α' ]) α'')))
                 (cong (λ ?x → ε - ?x) (sym γ))
                 (ξ , β) 

  seperated :
    (h g : liftNonexpanding₂Type) →
    ((ε : ℚ) (φ : 0 < ε) → liftNonexpanding₂Relation h g ε φ) → h ≡ g
  seperated (h , _) (g , _) ω =
    Σ≡Prop (λ h → isPropΠ5 (λ ε φ u v _ → squash ε φ (h u) (h v)))
           (funExt (λ u → path (h u) (g u) (λ ε φ → ω ε φ u)))

  rationalRationalCase :
    (q r ε : ℚ) (ω : 0 < ε) →
    - ε < q - r → q - r < ε →
    liftNonexpanding₂Relation (rationalCase q) (rationalCase r) ε ω
  rationalRationalCase q r ε ω χ π w =
    inductionProposition {A = P} (ρ , σ , τ) w ε ω χ π
    where
    P : ℝ → Type ℓ-zero
    P w = (ε : ℚ) (ω : 0 < ε) →
          - ε < q - r → q - r < ε →
          Close ε ω (fst (rationalCase q) w) (fst (rationalCase r) w)

    ρ : (s : ℚ) → 
        (ε : ℚ) (ω : 0 < ε) →
        - ε < q - r → q - r < ε →
        Close ε ω (fst (rationalCase q) (rational s))
                  (fst (rationalCase r) (rational s))
    ρ s ε ω χ π = τ'
      where
      σ : ∣ f q s - f r s ∣ ≤ ∣ q - r ∣
      σ = φ s q r

      τ : ∣ f q s - f r s ∣ < ε
      τ = isTrans≤<
            ∣ f q s - f r s ∣ ∣ q - r ∣ ε
            σ (<→∣∣< {x = q - r} {ε = ε} π χ)

      τ' : Close ε ω (rational (f q s)) (rational (f r s))
      τ' = rationalRational
             (f q s) (f r s) ε ω
             (∣∣<→<₂ {x = f q s - f r s} {ε = ε} τ)
             (∣∣<→<₁ {x = f q s - f r s} {ε = ε} τ)

    σ : (x : (ε : ℚ) → 0 < ε → ℝ) (τ : CauchyApproximation x) →
        ((δ : ℚ) (υ : 0 < δ)
         (ε : ℚ) (ω : 0 < ε) → 
         - ε < q - r → q - r < ε →
         Close ε ω (fst (rationalCase q) (x δ υ))
                   (fst (rationalCase r) (x δ υ))) →
        (ε : ℚ) (ω : 0 < ε) →
        - ε < q - r → q - r < ε →
        Close ε ω (fst (rationalCase q) (limit x τ))
                  (fst (rationalCase r) (limit x τ))
    σ x τ υ ε ω χ π =
      ∃-rec
        (squash ε ω (fst (rationalCase q) (limit x τ))
                    (fst (rationalCase r) (limit x τ)))
        ο
        ξ
      where
      ξ' : ∣ q - r ∣ < ε
      ξ' = <→∣∣< {x = q - r} {ε = ε} π χ

      ξ : ∃ ℚ (λ θ → (0 < θ) × Σ (0 < ε - θ) (λ ψ → ∣ q - r ∣ < ε - θ))
      ξ = ∣ ∣∣<-open (q - r) ε ω ξ' ∣₁

      ο : (θ : ℚ) →
          (0 < θ) × Σ (0 < ε - θ) (λ ψ → ∣ q - r ∣ < ε - θ) →
          Close ε ω
                (fst (rationalCase q) (limit x τ))
                (fst (rationalCase r) (limit x τ))
      ο θ (α , β , γ) =
        -- Sneaky! Figuring out what to put for the Cauchy approximations here
        -- took *days*. Turns out we can consider the cauchy approximation given
        -- by applying the functions lift(rational ∘ (f q)) and lift(rational ∘
        -- (f q)) to the Cauchy approximation x at a particular ε. Not at all
        -- obvious me thinks.
        limitLimit
          (liftLipschitzApproximation
            (λ ε ζ → fst (rationalCase q) (x ε ζ)) 1 η')
          (liftLipschitzApproximation
            (λ ε ζ → fst (rationalCase r) (x ε ζ)) 1 η')
          _
          _
          ε θ' θ' ω ζ'' ζ'' (fst κ') (snd κ')
        where
        ζ : ¬ 2 ≡ 0
        ζ = Bool.toWitnessFalse {Q = discreteℚ 2 0} tt 

        η : ¬ 1 ≡ 0
        η = Bool.toWitnessFalse {Q = discreteℚ 1 0} tt

        ζ' : 0 < 2
        ζ' = Bool.toWitness {Q = <Dec 0 2} tt

        η' : 0 < 1
        η' = Bool.toWitness {Q = <Dec 0 1} tt

        θ' = θ / 2 [ ζ ]

        θ'' = θ' / 1 [ η ]

        ζ'' : 0 < θ'
        ζ'' = 0</' {x = θ} {y = 2} α ζ'

        η'' : 0 < θ''
        η'' = 0</' {x = θ'} {y = 1} ζ'' η'

        ι : θ' + θ' ≡ θ
        ι = self/2≡self θ ζ

        ι' : ε - θ ≡ ε - (θ' + θ')
        ι' = cong (_-_ ε) (sym ι)

        κ : Close (ε - θ) β
                  (fst (rationalCase q) (x θ'' η''))
                  (fst (rationalCase r) (x θ'' η''))
        κ = υ θ'' η'' (ε - θ) β
              (∣∣<→<₂ {x = q - r} {ε = ε - θ} γ)
              (∣∣<→<₁ {x = q - r} {ε = ε - θ} γ)

        κ' : Σ (0 < ε - (θ' + θ'))
               (λ ξ →
                 Close (ε - (θ' + θ')) ξ
                       (fst (rationalCase q) (x θ'' η''))       
                       (fst (rationalCase r) (x θ'' η'')))
        κ' = subst (λ ?x → Σ (0 < ?x)
                     (λ ξ → Close ?x ξ (fst (rationalCase q) (x θ'' η''))
                                       (fst (rationalCase r) (x θ'' η''))))
                   ι'
                   (β , κ)

    τ : (w : ℝ) →
        isProp
          ((ε : ℚ) (ω : 0 < ε) →
           - ε < q - r → q - r < ε →
           Close ε ω (fst (rationalCase q) w) (fst (rationalCase r) w))
    τ w = isPropΠ4
            (λ ε ω χ π →
              squash ε ω (fst (rationalCase q) w) (fst (rationalCase r) w))

  rationalLimitCase :
    (q ε δ : ℚ) (ω : 0 < ε) (χ : 0 < δ) (π : 0 < ε - δ)
    (y : (ε₁ : ℚ) → 0 < ε₁ → ℝ) (ρ : CauchyApproximation y)
    (g : (ε₁ : ℚ) → 0 < ε₁ → liftNonexpanding₂Type)
    (σ : CauchyApproximation'' liftNonexpanding₂Type
                               liftNonexpanding₂Relation g) →
    Close (ε - δ) π (rational q) (y δ χ) →
    liftNonexpanding₂Relation (rationalCase q) (g δ χ) (ε - δ) π →
    liftNonexpanding₂Relation (rationalCase q) (limitCase y ρ g σ) ε ω
  rationalLimitCase q ε δ ω χ π y ρ g σ τ υ v =
    closeLimit'
      (fst (rationalCase q) v) (fLimit' g v)
      (fLimit'-cauchy g v σ) ε δ ω χ π α
    where
    α : Close (ε - δ) π (fst (rationalCase q) v) (fst (g δ χ) v)
    α = υ v

  limitRationalCase :
    (z : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation z)
    (h : (ε : ℚ) → 0 < ε → liftNonexpanding₂Type)
    (χ : CauchyApproximation'' liftNonexpanding₂Type
                               liftNonexpanding₂Relation h)
    (r ε δ : ℚ) (π : 0 < ε) (ρ : 0 < δ) (σ : 0 < ε - δ) →
    Close (ε - δ) σ (z δ ρ) (rational r) →
    liftNonexpanding₂Relation (h δ ρ) (rationalCase r) (ε - δ) σ →
    liftNonexpanding₂Relation (limitCase z ω h χ) (rationalCase r) ε π
  limitRationalCase z ω h χ r ε δ π ρ σ τ υ v =
    limitClose'
      (rationalCase r .fst v) (fLimit' h v)
      (fLimit'-cauchy h v χ) ε δ π ρ σ α
    where
    α : Close (ε - δ) σ (fLimit' h v δ ρ) (fst (rationalCase r) v)
    α = υ v

  limitLimitCase :
    (y z : (ε : ℚ) → 0 < ε → ℝ)
    (g h : (ε : ℚ) → 0 < ε → liftNonexpanding₂Type)
    (ω : CauchyApproximation y) (χ : CauchyApproximation z)
    (π : CauchyApproximation'' liftNonexpanding₂Type
                               liftNonexpanding₂Relation g)
    (ρ : CauchyApproximation'' liftNonexpanding₂Type
                               liftNonexpanding₂Relation h)
    (ε δ η : ℚ) (σ : 0 < ε) (τ : 0 < δ) (υ : 0 < η)
    (ξ : 0 < ε - (δ + η)) →
    Close (ε - (δ + η)) ξ (y δ τ) (z η υ) →
    liftNonexpanding₂Relation (g δ τ) (h η υ) (ε - (δ + η)) ξ →
    liftNonexpanding₂Relation (limitCase y ω g π) (limitCase z χ h ρ) ε σ
  limitLimitCase y z g h ω χ π ρ ε δ η σ τ υ ξ ο α v =
    limitLimit
      (fLimit' g v) (fLimit' h v)
      (fLimit'-cauchy g v π) (fLimit'-cauchy h v ρ)
      ε δ η σ τ υ ξ β
    where
    β : Close (ε - (δ + η)) ξ (fLimit' g v δ τ) (fLimit' h v η υ)
    β = (α v)

  relation :
    (h g : liftNonexpanding₂Type) (ε : ℚ) (φ : 0 < ε) →
    isProp (liftNonexpanding₂Relation h g ε φ)
  relation h g ε φ = isPropΠ (λ u → squash ε φ ((fst h) u) ((fst g) u))

liftNonexpanding₂ : 
  (f : ℚ → ℚ → ℚ) →
  Nonexpandingℚ₂ f →
  (ℝ → ℝ → ℝ)
liftNonexpanding₂ f φ = fst ∘ (recursion $ liftNonexpanding₂Recursion f φ)

liftNonexpanding₂NonExpanding : 
  (f : ℚ → ℚ → ℚ)
  (φ : Nonexpandingℚ₂ f) →
  Nonexpandingℝ₂ $ liftNonexpanding₂ f φ
liftNonexpanding₂NonExpanding f φ =
  (λ u v w ε ψ ω → recursion∼ (liftNonexpanding₂Recursion f φ) ω u) ,
  (λ u v w ε ψ →
    let
      ω : (ε : ℚ) (χ : 0 < ε) (v w : ℝ) →
          Close ε χ v w →
          Close ε χ (liftNonexpanding₂ f φ u v) (liftNonexpanding₂ f φ u w)
      ω = snd $ (recursion $ liftNonexpanding₂Recursion f φ) u

      χ : Close ε ψ v w →
          Close ε ψ (liftNonexpanding₂ f φ u v) (liftNonexpanding₂ f φ u w)
      χ = ω ε ψ v w
    in χ)

liftNonexpanding₂≡rational : 
  (f : ℚ → ℚ → ℚ)
  (φ : Nonexpandingℚ₂ f)
  (q r : ℚ) →
  ((liftNonexpanding₂ f φ) (rational q) (rational r) ≡ rational (f q r))
liftNonexpanding₂≡rational f φ q r = refl
