module HoTTReals.Data.Real.Close.Other where

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
open import HoTTReals.Data.Real.Close.CloseAlternative
open import HoTTReals.Data.Real.Close.ReflexiveSymmetric
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ

Close' : (ε : ℚ) → 0 < ε → ℝ → ℝ → Type ℓ-zero
Close' = fst Close'Σ

syntax Close' ε p x y = x ≈[ ε , p ] y

close'RationalRationalDefinition :
  (q r : ℚ) (ε : ℚ) (φ : 0 < ε) →
  (rational q ≈[ ε , φ ] rational r) ≡ (∣ q - r ∣ < ε)
close'RationalRationalDefinition q r ε φ = refl

close'RationalLimitDefinition :
  (q : ℚ)
  (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
  (ε : ℚ) (ψ : 0 < ε) →
  (rational q ≈[ ε , ψ ] limit y φ) ≡
  ∃ ℚ (λ δ → Σ (0 < δ) (λ ω →
             Σ (0 < ε - δ)
             (λ χ → rational q ≈[ ε - δ , χ ] y δ ω)))
close'RationalLimitDefinition q x φ ε ψ = refl

close'LimitRationalDefinition :
  (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
  (r : ℚ)
  (ε : ℚ) (ψ : 0 < ε) →
  (limit x φ ≈[ ε , ψ ] rational r) ≡
  (∃ ℚ (λ δ → Σ (0 < δ) (λ ω →
             Σ (0 < ε - δ)
             (λ χ → x δ ω ≈[ ε - δ , χ ] rational r))))
close'LimitRationalDefinition x φ r ε ψ = refl

close'LimitLimitDefinition :
  (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
  (y : (ε : ℚ) → 0 < ε → ℝ) (ψ : CauchyApproximation y)
  (ε : ℚ) (ω : 0 < ε) →
  (limit x φ ≈[ ε , ω ] limit y ψ) ≡
  (∃ (ℚ × ℚ)
    (λ where (δ , η) → Σ (0 < δ)
                (λ χ → Σ (0 < η)
                (λ π → Σ (0 < ε - (δ + η))
                (λ σ → x δ χ ≈[ (ε - (δ + η)) , σ ] y η π)))))
close'LimitLimitDefinition x φ y ψ ε ω = refl

close'Proposition : (ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close' ε φ u v)
close'Proposition = fst $ snd $ Close'Σ

close'Rounded : Rounded Close' close'Proposition
close'Rounded = fst $ snd $ snd $ Close'Σ

close'TriangleInequality₁ :
  TriangleInequality₁ Close Close' squash close'Proposition
close'TriangleInequality₁ = snd $ snd $ snd $ Close'Σ

close→close' : (u v : ℝ) (ε : ℚ) (φ : 0 < ε) →
               u ∼[ ε , φ ] v → u ≈[ ε , φ ] v
close→close' u v ε φ =
  induction∼ {B = λ {u} {v} {ε} {φ} ψ → Close' ε φ u v}
             (rationalRationalCase ,
              rationalLimitCase ,
              limitRationalCase ,
              limitLimitCase ,
              proposition)
  where
  rationalRationalCase :
    (q r ε : ℚ) (φ : 0 < ε) →
    - ε < q - r → q - r < ε →
    Close' ε φ (rational q) (rational r)
  rationalRationalCase q r ε φ ψ ω = <→∣∣< {x = q - r} {ε = ε} ω ψ

  rationalLimitCase :
    (q δ ε : ℚ) (φ : 0 < δ) (ψ : 0 < ε) (ω : 0 < ε - δ)
    (y : (ε : ℚ) → 0 < ε → ℝ) (χ : CauchyApproximation y) →
    Close (ε - δ) ω (rational q) (y δ φ) →
    Close' (ε - δ) ω (rational q) (y δ φ) →
    Close' ε ψ (rational q) (limit y χ)
  rationalLimitCase q δ ε φ ψ ω y χ π ρ = ∣ δ , (φ , ω , ρ) ∣₁

  limitRationalCase :
    (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
    (r δ ε : ℚ) (ψ : 0 < δ) (ω : 0 < ε) (χ : 0 < ε - δ) →
    Close (ε - δ) χ (x δ ψ) (rational r) →
    Close' (ε - δ) χ (x δ ψ) (rational r) →
    Close' ε ω (limit x φ) (rational r)
  limitRationalCase x φ r δ ε ψ ω χ π ρ = ∣ δ , (ψ , χ , ρ) ∣₁

  limitLimitCase :
    (x y : (ε : ℚ) → 0 < ε → ℝ)
    (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
    (ε δ η : ℚ) (ω : 0 < ε) (χ : 0 < δ) (π : 0 < η)
    (ρ : 0 < ε - (δ + η)) →
    Close (ε - (δ + η)) ρ (x δ χ) (y η π) →
    Close' (ε - (δ + η)) ρ (x δ χ) (y η π) →
    Close' ε ω (limit x φ) (limit y ψ)
  limitLimitCase x y φ ψ ε δ η ω χ π ρ σ τ =
    ∣ (δ , η) , (χ , π , ρ , τ) ∣₁

  proposition :
    (u v : ℝ) (ε : ℚ) (φ : 0 < ε) →
    Close ε φ u v → isProp (Close' ε φ u v)
  proposition u v ε φ _ = close'Proposition ε φ u v

close'→close : (u v : ℝ) (ε : ℚ) (φ : 0 < ε) →
               u ≈[ ε , φ ] v → u ∼[ ε , φ ] v
close'→close =
  inductionProposition₂
    {A = λ u v → (ε : ℚ) (φ : 0 < ε) → Close' ε φ u v → Close ε φ u v}
    (rationalRationalCase ,
     rationalLimitCase ,
     limitRationalCase ,
     limitLimitCase ,
     proposition)
  where
  rationalRationalCase :
    (q r ε : ℚ) (φ : 0 < ε) →
    Close' ε φ (rational q) (rational r) →
    Close ε φ (rational q) (rational r)
  rationalRationalCase q r ε φ ψ =
    rationalRational q r ε φ
      (∣∣<→<₂ {x = q - r} {ε = ε} ψ) (∣∣<→<₁ {x = q - r} {ε = ε} ψ)

  rationalLimitCase :
    (q : ℚ)
    (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y) →
    ((ε : ℚ) (ψ : 0 < ε) (δ : ℚ) (ω : 0 < δ) →
     Close' δ ω (rational q) (y ε ψ) →
     Close δ ω (rational q) (y ε ψ)) →
    (ε : ℚ) (ω : 0 < ε) →
    Close' ε ω (rational q) (limit y φ) →
    Close ε ω (rational q) (limit y φ)
  rationalLimitCase q y φ ψ ε ω =
    ∃-rec (squash ε ω (rational q) (limit y φ))
          rationalLimitCase'
    where
    rationalLimitCase' :
      (η : ℚ) →
      Σ (0 < η) (λ χ → Σ (0 < ε - η) (λ π → rational q ≈[ ε - η , π ] y η χ)) →
      Close ε ω (rational q) (limit y φ)
    rationalLimitCase' η (χ , π , ρ) =
      rationalLimit q ε η ω χ π y φ (ψ η χ (ε - η) π ρ)

  limitRationalCase :
    (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
    (r : ℚ) →
    ((ε : ℚ) (ψ : 0 < ε) (δ : ℚ) (ω : 0 < δ) →
     Close' δ ω (x ε ψ) (rational r) →
     Close δ ω (x ε ψ) (rational r)) →
    (ε : ℚ) (ω : 0 < ε) →
    Close' ε ω (limit x φ) (rational r) →
    Close ε ω (limit x φ) (rational r)
  limitRationalCase x φ r ψ ε ω =
    ∃-rec (squash ε ω (limit x φ) (rational r))
          limitRationalCase'
    where
    limitRationalCase' :
      (η : ℚ) →
      Σ (0 < η) (λ χ → Σ (0 < ε - η) (λ π → x η χ ≈[ ε - η , π ] rational r)) →
      Close ε ω (limit x φ) (rational r)
    limitRationalCase' η (χ , π , ρ) =
      limitRational x φ r ε η ω χ π (ψ η χ (ε - η) π ρ)
  
  limitLimitCase :
    (x y : (ε : ℚ) → 0 < ε → ℝ)
    (φ : CauchyApproximation x)
    (ψ : CauchyApproximation y) →
    ((ε δ : ℚ) (ω : 0 < ε) (χ : 0 < δ)
     (η : ℚ) (π : 0 < η) →
     Close' η π (x ε ω) (y δ χ) → Close η π (x ε ω) (y δ χ)) →
    (ε : ℚ) (χ : 0 < ε) →
    Close' ε χ (limit x φ) (limit y ψ) →
    Close ε χ (limit x φ) (limit y ψ)
  limitLimitCase x y φ ψ ω ε χ =
    ∃-rec (squash ε χ (limit x φ) (limit y ψ))
          limitLimitCase'
    where
    limitLimitCase' :
      (θη : ℚ × ℚ) →
      Σ (0 < fst θη)
      (λ π →
      Σ (0 < snd θη)
      (λ ρ →
      Σ (0 < ε - (fst θη + snd θη))
      λ σ → x (fst θη) π ≈[ ε - (fst θη + snd θη) , σ ] y (snd θη) ρ)) →
      Close ε χ (limit x φ) (limit y ψ)
    limitLimitCase' (θ , η) (π , ρ , σ , τ) =
      limitLimit x y φ ψ ε θ η χ π ρ σ (ω θ η π ρ (ε - (θ + η)) σ τ)

  proposition :
    (u v : ℝ) → isProp ((ε : ℚ) (φ : 0 < ε) → Close' ε φ u v → Close ε φ u v)
  proposition u v = isPropΠ3 (λ ε φ _ → squash ε φ u v)

close≃close' : (ε : ℚ) (φ : 0 < ε) (u v : ℝ) →
               u ∼[ ε , φ ] v ≃ u ≈[ ε , φ ] v
close≃close' ε φ u v =
  propBiimpl→Equiv (squash ε φ u v) (close'Proposition ε φ u v)
                   (close→close' u v ε φ) (close'→close u v ε φ)
                   
close≡close' : (ε : ℚ) (φ : 0 < ε) (u v : ℝ) →
               u ∼[ ε , φ ] v ≡ u ≈[ ε , φ ] v
close≡close' ε φ u v = ua (close≃close' ε φ u v)

close≡close'' : Close ≡ Close'
close≡close'' =
  funExt (λ ε → funExt (λ φ → funExt (λ u → funExt λ v → close≡close' ε φ u v)))

closeRounded : Rounded Close squash
closeRounded = ω
  where
  ψ : Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close ε φ u v))
        (Rounded Close)
  ψ = subst (λ ?x → Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (?x ε φ u v))
                      (Rounded ?x))
            (sym $ close≡close'')
            (close'Proposition , close'Rounded)

  ω : Rounded Close squash
  ω = subst (λ ?x → Rounded Close ?x)
            (isPropΠ4 (λ ε φ u v → isPropIsProp) (fst ψ) squash)
            (snd ψ)

closeOpen : Open Close squash
closeOpen u v ε φ = fst $ closeRounded u v ε φ

closeTriangleInequality : TriangleInequality Close squash
closeTriangleInequality = ψ
  where
  φ : Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close ε φ u v))
        (TriangleInequality₁ Close Close squash)
  φ = subst (λ ?x → Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (?x ε φ u v))
                      (TriangleInequality₁ Close ?x squash))
            (sym $ close≡close'')
            (close'Proposition , close'TriangleInequality₁) 

  ψ : TriangleInequality₁ Close Close squash squash
  ψ = subst (TriangleInequality₁ Close Close squash)
            (isPropΠ4 (λ ε φ u v → isPropIsProp) (fst φ) squash)
            (snd φ)

close'TriangleInequality : TriangleInequality Close' close'Proposition
close'TriangleInequality = ψ
  where
  φ : Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (Close' ε φ u v))
        (λ ?x → TriangleInequality₁ Close' Close' ?x close'Proposition)
  φ = subst (λ ?x →
               Σ ((ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp (?x ε φ u v))
                 (λ ?y → TriangleInequality₁ ?x Close' ?y close'Proposition))
            (close≡close'')
            (squash , close'TriangleInequality₁) 

  ψ : TriangleInequality₁ Close' Close' close'Proposition close'Proposition
  ψ = subst (λ ?x → TriangleInequality₁ Close' Close' ?x close'Proposition)
            ((isPropΠ4 (λ ε φ u v → isPropIsProp) (fst φ) close'Proposition))
            (snd φ)

closeLimit : (u : ℝ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
             (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) →
             u ∼[ ε , ψ ] (y δ ω) →
             u ∼[ ε + δ , 0<+' {x = ε} {y = δ} ψ ω ] (limit y φ)
closeLimit =
  inductionProposition
    (closeLimitRational ,
     closeLimitLimit ,
     closeLimitProposition)
  where
  closeLimitRational :
    (q : ℚ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
    (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) →
    Close ε ψ (rational q) (y δ ω) →
    Close (ε + δ) (0<+' {x = ε} {y = δ} ψ ω) (rational q) (limit y φ)
  closeLimitRational q y φ ε δ ψ ω χ =
    rationalLimit q (ε + δ) δ (0<+' {x = ε} {y = δ} ψ ω) ω (fst π) y φ (snd π)
    where
    π : Σ (0 < (ε + δ) - δ)
          (λ ρ → Close ((ε + δ) - δ) ρ (rational q) (y δ ω))
    π = subst (λ ?x → Σ (0 < ?x) (λ ρ → Close ?x ρ (rational q) (y δ ω)))
              (sym $ addSubtractRightCancel ε δ)
              (ψ , χ)

  closeLimitLimit :
    (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x) →
    ((ε : ℚ) (ψ : 0 < ε) (y : (ε : ℚ) → 0 < ε → ℝ)
     (ω : CauchyApproximation y) (δ η : ℚ) (χ : 0 < δ) (π : 0 < η) →
     Close δ χ (x ε ψ) (y η π) →
     Close (δ + η) (0<+' {x = δ} {y = η} χ π) (x ε ψ) (limit y ω)) →
    (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) (ε δ : ℚ)
    (χ : 0 < ε) (π : 0 < δ) →
    Close ε χ (limit x φ) (y δ π) →
    Close (ε + δ) (0<+' {x = ε} {y = δ} χ π) (limit x φ) (limit y ω)
  closeLimitLimit x φ ψ y ω ε δ χ π ρ =
    ∃-rec (squash (ε + δ) (0<+' {x = ε} {y = δ} χ π) (limit x φ) (limit y ω))
          closeLimitLimit'
          (closeOpen (limit x φ) (y δ π) ε χ ρ)
    where
    closeLimitLimit' :
      (θ : ℚ) →
      Σ (0 < θ)
      (λ σ →
      Σ (0 < ε - θ)
      (λ τ → Close (ε - θ) τ (limit x φ) (y δ π))) →
      Close (ε + δ) (0<+' {x = ε} {y = δ} χ π) (limit x φ) (limit y ω)
    closeLimitLimit' θ (σ , τ , υ) =
      limitLimit x y φ ω (ε + δ) (θ / 3 [ β ]) δ
        (0<+' {x = ε} {y = δ} χ π) β'' π (fst ζ') (snd ζ')
      where
      α : (η ϕ : ℚ) (τ : 0 < η) (υ : 0 < ϕ) →
          Close (η + ϕ) (0<+' {x = η} {y = ϕ} τ υ) (x η τ) (limit x φ)
      α η ϕ τ υ = γ'
        where
        β : Close (ϕ + η) (0<+' {x = ϕ} {y = η} υ τ) (x η τ) (limit x φ)
        β = ψ η τ x φ ϕ η υ τ (closeReflexive (x η τ) ϕ υ)

        γ : Σ (0 < η + ϕ) (λ ζ → Close (η + ϕ) ζ (x η τ) (limit x φ))
        γ = subst (λ ?x → Σ (0 < ?x) (λ ζ → Close ?x ζ (x η τ) (limit x φ)))
                  (+Comm ϕ η)
                  (0<+' {x = ϕ} {y = η} υ τ , β)

        γ' : Close (η + ϕ) (0<+' {x = η} {y = ϕ} τ υ) (x η τ) (limit x φ)
        γ' = subst (λ ?x → Close (η + ϕ) ?x (x η τ) (limit x φ))
                   (isProp< 0 (η + ϕ) (fst γ) (0<+' {x = η} {y = ϕ} τ υ))
                   (snd γ)

      β : ¬ 3 ≡ 0
      β = Bool.toWitnessFalse {Q = discreteℚ 3 0} tt

      β' : 0 < 3
      β' = Bool.toWitness {Q = <Dec 0 3} tt

      η : ℚ
      η = θ / 3 [ β ]

      β'' : 0 < η
      β'' = 0</ {x = θ} {y = 3} σ β'

      γ : x η β'' ∼[ η + η ,
                     0<+' {x = η} {y = η}
                          β'' β'' ]
          limit x φ
      γ = α η η β'' β''

      κ = 0<+' {x = η + η} {y = ε - θ}
               (0<+' {x = η} {y = η} β'' β'')
               τ

      ζ : Close ((η + η) + (ε - θ)) κ (x η β'') (y δ π)
      ζ = closeTriangleInequality
            (x η β'') (limit x φ) (y δ π)
            (η + η) (ε - θ)
            (0<+' {x = η} {y = η} β'' β'') τ
            γ υ

      ι : ((θ / 3 [ β ]) + (θ / 3 [ β ])) + (ε - θ) ≡ ε - (θ / 3 [ β ])
      ι = ((θ / 3 [ β ]) + (θ / 3 [ β ])) + (ε - θ)
            ≡⟨ addRightSwap (η + η) ε (- θ) ⟩
          ε + (((θ / 3 [ β ]) + (θ / 3 [ β ])) - θ) 
            ≡⟨ cong (λ ?x → ε + (?x - θ)) (self/3+self/3≡2/3self θ) ⟩
          ε + (((2 / 3 [ β ]) · θ) - θ) 
            ≡⟨ cong (_+_ ε) (subtract≡negateNegateAdd ((2 / 3 [ β ]) · θ) θ) ⟩
          ε - (θ - ((2 / 3 [ β ]) · θ)) 
            ≡⟨ cong (_-_ ε) (self-2/3self θ) ⟩
          ε - (θ / 3 [ β ]) ∎

      ι' : (ε + δ) - ((θ / 3 [ β ]) + δ) ≡ ε - (θ / 3 [ β ])
      ι' = (ε + δ) - ((θ / 3 [ β ]) + δ)
             ≡⟨ cong (_+_ (ε + δ)) (negateAdd (θ / 3 [ β ]) δ) ⟩
           (ε + δ) + (- (θ / 3 [ β ]) + - δ)
             ≡⟨ cong (_+_ (ε + δ)) (+Comm (- (θ / 3 [ β ])) (- δ)) ⟩
           (ε + δ) + (- δ + - (θ / 3 [ β ]))
             ≡⟨ +Assoc (ε + δ) (- δ) (- (θ / 3 [ β ])) ⟩
           ((ε + δ) + - δ) + - (θ / 3 [ β ])
             ≡⟨ cong (flip _+_ (- (θ / 3 [ β ])))
                     (addSubtractRightCancel ε δ) ⟩
           ε + - (θ / 3 [ β ]) ∎

      ζ' : Σ (0 < (ε + δ) - (η + δ))
             (λ ι → Close ((ε + δ) - (η + δ)) ι (x η β'') (y δ π))
      ζ' = subst (λ ?x → Σ (0 < ?x)
                           (λ μ → Close ?x μ (x η β'') (y δ π)))
                 (ι ∙ sym ι')
                 (κ , ζ)

  closeLimitProposition :
    (u : ℝ) →
    isProp ((y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y) (ε δ : ℚ)
            (ψ : 0 < ε) (ω : 0 < δ) →
            Close ε ψ u (y δ ω) →
            Close (ε + δ) (0<+' {x = ε} {y = δ} ψ ω) u (limit y φ))
  closeLimitProposition u =
    isPropΠ6 (λ y φ ε δ ψ ω →
                isProp→ (squash (ε + δ) (0<+' {x = ε} {y = δ} ψ ω)
                                u (limit y φ)))

closeLimit' : (u : ℝ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
              (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) (θ : 0 < ε - δ) →
              u ∼[ ε - δ , θ ] (y δ ω) →
              u ∼[ ε , ψ ] (limit y φ)
closeLimit' u y φ ε δ ψ ω θ χ = σ'
  where
  π : (ε - δ) + δ ≡ ε
  π = subtractAddRightCancel δ ε

  σ : Σ (0 < ε) (λ π → Close ε π u (limit y φ))
  σ = subst (λ ?x → Σ (0 < ?x) (λ π → Close ?x π u (limit y φ)))
            π
            (0<+' {x = ε - δ} {y = δ} θ ω ,
             closeLimit u y φ (ε - δ) δ θ ω χ)

  σ' : Close ε ψ u (limit y φ)
  σ' = subst (λ π → Close ε π _ _) (isProp< 0 ε (fst σ) ψ) (snd σ)

closeLimit'' : (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
               (δ η : ℚ) (ψ : 0 < δ) (ω : 0 < η) →
               y δ ψ ∼[ η + δ , 0<+' {x = η} {y = δ} ω ψ ] limit y φ
closeLimit'' y φ δ η ψ ω =
  closeLimit (y δ ψ) y φ η δ ω ψ (closeReflexive (y δ ψ) η ω)

limitClose : (u : ℝ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
             (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) →
             (y δ ω) ∼[ ε , ψ ] u →
             (limit y φ) ∼[ ε + δ , 0<+' {x = ε} {y = δ} ψ ω ] u
limitClose u y φ ε δ ψ ω χ =
  closeSymmetric u (limit y φ) (ε + δ) (0<+' {x = ε} {y = δ} ψ ω) π
  where
  π : u ∼[ ε + δ , 0<+' {x = ε} {y = δ} ψ ω ] (limit y φ)
  π = closeLimit u y φ ε δ ψ ω (closeSymmetric (y δ ω) u ε ψ χ)

limitClose' : (u : ℝ) (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
              (ε δ : ℚ) (ψ : 0 < ε) (ω : 0 < δ) (θ : 0 < ε - δ) →
              (y δ ω) ∼[ ε - δ , θ ] u →
              (limit y φ) ∼[ ε , ψ ] u
limitClose' u y φ ε δ ψ ω θ χ =
  closeSymmetric u (limit y φ) ε ψ π
  where
  π : u ∼[ ε , ψ ] (limit y φ)
  π = closeLimit' u y φ ε δ ψ ω θ (closeSymmetric (y δ ω) u (ε - δ) θ χ)

-- TODO: Change the argument order of δ and η it's confusing
limitClose'' : (y : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation y)
               (δ η : ℚ) (ψ : 0 < δ) (ω : 0 < η) →
               limit y φ ∼[ η + δ , 0<+' {x = η} {y = δ} ω ψ ] y δ ψ
limitClose'' y φ δ η ψ ω =
  limitClose (y δ ψ) y φ η δ ω ψ (closeReflexive (y δ ψ) η ω)
