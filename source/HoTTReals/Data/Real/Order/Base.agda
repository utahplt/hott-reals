module HoTTReals.Data.Real.Order.Base where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order

open BinaryRelation

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Real.Algebra.Lattice

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

_≤_ : ℝ → ℝ → Type ℓ-zero
_≤_ x y = max x y ≡ y

infix 4 _≤_ 

≤-isProp : (x y : ℝ) → isProp $ x ≤ y
≤-isProp x y = ℝ-isSet (max x y) y

≤-reflexive : isRefl _≤_
≤-reflexive = maxIdempotent

≤-antisymmetric : isAntisym _≤_
≤-antisymmetric x y φ ψ =
  x
    ≡⟨ sym ψ ⟩
  max y x
    ≡⟨ maxCommutative y x ⟩
  max x y
    ≡⟨ φ ⟩
  y ∎

≤-transitive : isTrans _≤_
≤-transitive x y z φ ψ =
  max x z
    ≡⟨ cong (max x) (sym ψ) ⟩
  max x (max y z)
    ≡⟨ sym $ maxAssociative x y z ⟩
  max (max x y) z
    ≡⟨ cong (flip max z) φ ⟩
  max y z
    ≡⟨ ψ ⟩
  z ∎

ℝ≤-isPoset : IsPoset _≤_
ℝ≤-isPoset = isposet ℝ-isSet ≤-isProp ≤-reflexive ≤-transitive ≤-antisymmetric

ℝ≤-posetStructure : PosetStr ℓ-zero ℝ
ℝ≤-posetStructure = posetstr _≤_ ℝ≤-isPoset

ℝ≤ : Poset ℓ-zero ℓ-zero
ℝ≤ = ℝ , ℝ≤-posetStructure

-- TODO: This shouldn't be a lemma we should just use properties of join
-- semilatice
≤-max₁ : (x y : ℝ) → x ≤ max x y
≤-max₁ x y =
  max x (max x y)
    ≡⟨ (sym $ maxAssociative x x y) ⟩
  max (max x x) y
    ≡⟨ cong (flip max y) (maxIdempotent x) ⟩
  max x y ∎

≤-max₂ : (x y : ℝ) → y ≤ max x y
≤-max₂ x y =
  max y (max x y)
    ≡⟨ cong (max y) (maxCommutative x y) ⟩
  max y (max y x)
    ≡⟨ (sym $ maxAssociative y y x) ⟩
  max (max y y) x
    ≡⟨ cong (flip max x) (maxIdempotent y) ⟩
  max y x
    ≡⟨ maxCommutative y x ⟩
  max x y ∎

_<_ : ℝ → ℝ → Type ℓ-zero
_<_ x y = ∃ (ℚ.ℚ × ℚ.ℚ)
            (λ where (q , r) → (x ≤ rational q) × (q ℚ.< r) × (rational r ≤ y))

infix 4 _<_ 

<-isProp : (x y : ℝ) → isProp $ x < y
<-isProp x y = isPropPropTrunc

-- TODO: I think there is an IsIsotone definition and we should probably use
-- that, but honestly a lot of the cubical library seems half baked
rationalMonotone :
  {q r : ℚ.ℚ} → q ℚ.≤ r → rational q ≤ rational r
rationalMonotone {q} {r} φ =
  ω
  where
  φ' : ℚ.max q r ≡ r
  φ' = ℚ.≤→max q r φ

  ψ : max (rational q) (rational r) ≡ rational (ℚ.max q r)
  ψ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ q r

  ω = max (rational q) (rational r)
        ≡⟨ ψ ⟩
      rational (ℚ.max q r)
        ≡⟨ cong rational φ' ⟩
      rational r ∎

rationalReflective :
  {q r : ℚ.ℚ} → rational q ≤ rational r → q ℚ.≤ r
rationalReflective {q} {r} φ = π
  where
  ψ : max (rational q) (rational r) ≡ rational (ℚ.max q r)
  ψ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ q r

  ω : rational (ℚ.max q r) ≡ rational r
  ω = sym ψ ∙ φ

  χ : ℚ.max q r ≡ r
  χ = rationalInjective ω

  π : q ℚ.≤ r
  π = ℚ.≡max→≤₂ {x = q} {y = r} χ

<→≤ : {x y : ℝ} → x < y → x ≤ y
<→≤ {x} {y} = ∃-rec (≤-isProp x y) φ
  where
  φ : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) × ((fst u) ℚ.< (snd u)) × (rational (snd u) ≤ y) →
      x ≤ y
  φ (q , r) (ψ , ω , χ) =
    ≤-transitive x (rational r) y
      (≤-transitive x (rational q) (rational r)
        ψ (rationalMonotone {q = q} {r = r} (ℚ.<Weaken≤ q r ω)))
      χ

<-irreflexive : isIrrefl _<_
<-irreflexive x φ = ∃-rec isProp⊥ ψ φ
  where
  ψ : (u : ℚ.ℚ × ℚ.ℚ) →
      ((x ≤ rational (fst u)) × (fst u ℚ.< snd u) × (rational (snd u) ≤ x)) →
      ⊥
  ψ (q , r) (ω , χ , π) = τ
    where
    ρ : rational r ≤ rational q
    ρ = ≤-transitive (rational r) x (rational q) π ω

    σ : r ℚ.≤ q
    σ = rationalReflective {q = r} {r = q} ρ

    τ : ⊥
    τ = ℚ.≤→≯ r q σ χ

<-transitive : isTrans _<_
<-transitive x y z φ ψ = ∃-rec (<-isProp x z) ω ψ
  where
  ω : (u : ℚ.ℚ × ℚ.ℚ) →
      ((y ≤ rational (fst u)) ×
       ((fst u) ℚ.< (snd u)) ×
       (rational (snd u) ≤ z)) →
      x < z
  ω (s , t) (σ , τ , υ) =
    ∣ (s , t) ,
      ((≤-transitive x y (rational s) (<→≤ {x = x} {y = y} φ) σ) , τ , υ) ∣₁

<-archimedian :
  (x y : ℝ) → x < y → ∃ ℚ.ℚ (λ q → (x < rational q) × (rational q < y))
<-archimedian x y φ = ∃-rec isPropPropTrunc ψ φ
  where
  ψ : (u : ℚ.ℚ × ℚ.ℚ) →
      ((x ≤ rational (fst u)) ×
       ((fst u) ℚ.< (snd u)) ×
       (rational (snd u) ≤ y)) →
      ∃ ℚ.ℚ (λ q → (x < rational q) × (rational q < y))
  ψ (q , r) (ω , χ , π) = ∣ m , (ρ , σ) ∣₁
    where
    m : ℚ.ℚ
    m = (q ℚ.+ r) / 2 [ ℚ.2≠0 ]

    ρ : x < rational m
    ρ = ∣ (q , m) ,
          (ω ,
           (ℚ.<→<-midpoint {x = q} {y = r} χ) ,
           (≤-reflexive $ rational m)) ∣₁

    σ : rational m < y
    σ = ∣ (m , r) ,
          ((≤-reflexive $ rational m) ,
           (ℚ.<→midpoint-< {x = q} {y = r} χ) ,
           π) ∣₁

rationalStrictMonotone : {q r : ℚ.ℚ} → q ℚ.< r → rational q < rational r
rationalStrictMonotone {q} {r} φ =
  ∣ ((q , r) , (≤-reflexive $ rational q) , φ , (≤-reflexive $ rational r)) ∣₁

rationalStrictReflective : {q r : ℚ.ℚ} → rational q < rational r → q ℚ.< r
rationalStrictReflective {q} {r} φ =
  ∃-rec (ℚ.isProp< q r) ψ φ
  where
  ψ : (u : ℚ.ℚ × ℚ.ℚ) →
      (rational q ≤ rational (fst u)) ×
      (fst u ℚ.< snd u) ×
      (rational (snd u) ≤ rational r) →
      q ℚ.< r
  ψ (s , t) (ω , χ , π) = ρ
    where
    ω' : q ℚ.≤ s
    ω' = rationalReflective {q = q} {r = s} ω

    π' : t ℚ.≤ r
    π' = rationalReflective {q = t} {r = r} π

    ρ : q ℚ.< r
    ρ = ℚ.isTrans≤< q s r ω' (ℚ.isTrans<≤ s t r χ π')

≤→<→< : {x y z : ℝ} → x ≤ y → y < z → x < z
≤→<→< {x} {y} {z} φ ψ = ∃-rec (<-isProp x z) ω ψ
  where
  ω : (u : ℚ.ℚ × ℚ.ℚ) →
      (y ≤ rational (fst u)) × ((fst u) ℚ.< (snd u)) × (rational (snd u) ≤ z) →
      x < z
  ω (q , r) (χ , π , ρ) =
    ∣ ((q , r) ,
      ((≤-transitive x y (rational q) φ χ) , π , ρ)) ∣₁

<→≤→< : {x y z : ℝ} → x < y → y ≤ z → x < z
<→≤→< {x} {y} {z} φ ψ = ∃-rec (<-isProp x z) ω φ
  where
  ω : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) × ((fst u) ℚ.< (snd u)) × (rational (snd u) ≤ y) →
      x < z
  ω (q , r) (χ , π , ρ) =
    ∣ ((q , r) ,
      (χ , π , ≤-transitive (rational r) y z ρ ψ)) ∣₁

≤rational→close→≤rational+ε :
  {q : ℚ.ℚ} {x y : ℝ} {ε : ℚ.ℚ}
  (φ : 0 ℚ.< ε) →
  x ≤ rational q →
  x ∼[ ε , φ ] y →
  y ≤ rational (q ℚ.+ ε)
≤rational→close→≤rational+ε {q} {x} {y} {ε} φ ψ ω = σ
  where
  χ : {q r : ℚ.ℚ} {y : ℝ} {ε : ℚ.ℚ}
      (φ : 0 ℚ.< ε) →
      rational r ≤ rational q →
      rational r ∼[ ε , φ ] y →
      y ≤ rational (q ℚ.+ ε)
  χ {q} {r} {y} {ε} φ ψ = inductionProposition {A = P} (χ' , χ'' , χ''') y
    where
    P : ℝ → Type ℓ-zero
    P y = rational r ∼[ ε , φ ] y → y ≤ rational (q ℚ.+ ε)

    χ' : (s : ℚ.ℚ) →
         rational r ∼[ ε , φ ] rational s →
         rational s ≤ rational (q ℚ.+ ε)
    χ' s π = υ'
      where
      π' : ℚ.∣ r ℚ.- s ∣ ℚ.< ε
      π' = close→close' (rational r) (rational s) ε φ π

      ρ : s ℚ.- r ℚ.≤ ℚ.∣ r ℚ.- s ∣
      ρ = subst (flip ℚ._≤_ ℚ.∣ r ℚ.- s ∣)
                (ℚ.negateSubtract' r s)
                (ℚ.≤max' (r ℚ.- s) (ℚ.- (r ℚ.- s)))

      σ : r ℚ.+ (s ℚ.- r) ℚ.≤ r ℚ.+ ℚ.∣ r ℚ.- s ∣
      σ = ℚ.≤-o+ (s ℚ.- r) ℚ.∣ r ℚ.- s ∣ r ρ

      σ' : s ℚ.≤ r ℚ.+ ℚ.∣ r ℚ.- s ∣
      σ' = subst (flip ℚ._≤_ $ r ℚ.+ ℚ.∣ r ℚ.- s ∣)
                 (ℚ.addLeftSubtractCancel r s)
                 σ

      τ : r ℚ.+ ℚ.∣ r ℚ.- s ∣ ℚ.≤ q ℚ.+ ε
      τ = ℚ.+≤+ {x = r} {y = q} {z = ℚ.∣ r ℚ.- s ∣} {w = ε}
              (rationalReflective {q = r} {r = q} ψ)
              (ℚ.<Weaken≤ ℚ.∣ r ℚ.- s ∣ ε π')

      υ : s ℚ.≤ q ℚ.+ ε
      υ = ℚ.isTrans≤ s (r ℚ.+ ℚ.∣ r ℚ.- s ∣) (q ℚ.+ ε) σ' τ

      υ' : rational s ≤ rational (q ℚ.+ ε)
      υ' = rationalMonotone {q = s} {r = q ℚ.+ ε} υ

    χ'' : (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (ω : CauchyApproximation x) →
          ((δ : ℚ.ℚ) (χ : 0 ℚ.< δ) →
           rational r ∼[ ε , φ ] x δ χ →
           x δ χ ≤ rational (q ℚ.+ ε)) →
          rational r ∼[ ε , φ ] limit x ω →
          limit x ω ≤ rational (q ℚ.+ ε)
    χ'' x ω χ π =
      ∃-rec (≤-isProp (limit x ω) (rational (q ℚ.+ ε)))
            ρ
            π'
      where
      π' : ∃ ℚ.ℚ
             (λ θ → (0 ℚ.< θ) ×
                  Σ (0 ℚ.< (ε ℚ.- θ))
                    (λ ξ → Close (ε ℚ.- θ) ξ (rational r) (limit x ω)))
      π' = closeOpen (rational r) (limit x ω) ε φ π

      ρ : (θ : ℚ.ℚ) →
          (0 ℚ.< θ) ×
          Σ (0 ℚ.< (ε ℚ.- θ))
          (λ ξ → Close (ε ℚ.- θ) ξ (rational r) (limit x ω)) →
          limit x ω ≤ rational (q ℚ.+ ε)
      ρ θ (σ , τ , υ) = γ
        where
        ο : (δ : ℚ.ℚ) (ξ : 0 ℚ.< δ) →
            δ ℚ.< θ →
            rational r ∼[ ε , φ ] x δ ξ
        ο δ ξ ο = γ''
          where
          α : 0 ℚ.< (θ ℚ.- δ) ℚ.+ δ
          α = ℚ.0<+' {x = θ ℚ.- δ} {y = δ} (ℚ.<→0<- {x = δ} {y = θ} ο) ξ

          β : limit x ω ∼[ (θ ℚ.- δ) ℚ.+ δ , α ] x δ ξ
          β = limitClose'' x ω δ (θ ℚ.- δ) ξ (ℚ.<→0<- {x = δ} {y = θ} ο)

          γ  : rational r ∼[ (ε ℚ.- θ) ℚ.+ ((θ ℚ.- δ) ℚ.+ δ) ,
                             ℚ.0<+' {x = ε ℚ.- θ} τ α ]
               x δ ξ
          γ = closeTriangleInequality
              (rational r) (limit x ω) (x δ ξ)
                (ε ℚ.- θ) ((θ ℚ.- δ) ℚ.+ δ) τ α
                υ β

          ζ : (ε ℚ.- θ) ℚ.+ ((θ ℚ.- δ) ℚ.+ δ) ≡ ε
          ζ = (ε ℚ.- θ) ℚ.+ ((θ ℚ.- δ) ℚ.+ δ)
                 ≡⟨ cong (ℚ._+_ (ε ℚ.- θ)) (ℚ.subtractAddRightCancel δ θ) ⟩
              (ε ℚ.- θ) ℚ.+ θ
                 ≡⟨ ℚ.subtractAddRightCancel θ ε ⟩
              ε ∎

          γ' : Σ (0 ℚ.< ε) (λ ι → rational r ∼[ ε , ι ] x δ ξ)
          γ' = subst (λ ?x → Σ (0 ℚ.< ?x)
                               (λ ι → rational r ∼[ ?x , ι ] x δ ξ))
                     ζ
                     ((ℚ.0<+' {x = ε ℚ.- θ} τ α) , γ) 

          γ'' : rational r ∼[ ε , φ ] x δ ξ
          γ'' = subst (λ ?φ → rational r ∼[ ε , ?φ ] x δ ξ)
                      (ℚ.isProp< 0 ε (fst γ') φ)
                      (snd γ')

        z : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ
        z = λ δ ζ → max (rational $ q ℚ.+ ε) (x δ ζ)

        ξ : EventuallyConstantAt θ σ z (rational $ q ℚ.+ ε)
        ξ δ ψ ω = maxCommutative (rational $ q ℚ.+ ε) (x δ ψ) ∙ χ δ ψ (ο δ ψ ω)

        ξ' : EventuallyConstantAt θ σ
               (liftLipschitzApproximation z 1 ℚ.0<1)
               (rational $ q ℚ.+ ε)
        ξ' δ ψ ω = γ'
          where
          α = ≠-symmetric $ ℚ.<→≠ ℚ.0<1

          β = ℚ.0</ {x = δ} {y = 1} ψ ℚ.0<1

          γ : Σ (0 ℚ.< δ / 1 [ α ])
                   (λ ?φ → max (rational $ q ℚ.+ ε) (x (δ / 1 [ α ]) ?φ) ≡
                           (rational $ q ℚ.+ ε))
          γ = subst (λ ?δ → Σ (0 ℚ.< ?δ)
                                 (λ ?φ → max (rational $ q ℚ.+ ε) (x ?δ ?φ) ≡
                                         (rational $ q ℚ.+ ε)))
                       (sym $ ℚ.·IdR δ)
                       (ψ , ξ δ ψ ω)

          γ' : max (rational $ q ℚ.+ ε) (x (δ / 1 [ α ]) β) ≡
                   (rational $ q ℚ.+ ε)
          γ' = subst (λ ?φ →
                        max (rational $ q ℚ.+ ε) (x (δ / 1 [ α ]) ?φ) ≡
                          (rational $ q ℚ.+ ε))
                        (ℚ.isProp< 0 (δ / 1 [ α ]) (fst γ) β)
                        (snd γ)

        α : max (rational $ q ℚ.+ ε) (limit x ω) ≡
            limit (liftLipschitzApproximation z 1 ℚ.0<1) _
        α = refl

        β : limit (liftLipschitzApproximation z 1 ℚ.0<1) _ ≡ rational (q ℚ.+ ε)
        β = eventuallyConstantAt≡constant
              θ σ
              (liftLipschitzApproximation z 1 ℚ.0<1) _
              (rational $ q ℚ.+ ε)
              ξ'

        γ : max (limit x ω) (rational $ q ℚ.+ ε) ≡ rational (q ℚ.+ ε)
        γ = max (limit x ω) (rational $ q ℚ.+ ε)
              ≡⟨ maxCommutative (limit x ω) (rational $ q ℚ.+ ε) ⟩
            max (rational $ q ℚ.+ ε) (limit x ω)
              ≡⟨ α ⟩
            limit (liftLipschitzApproximation z 1 ℚ.0<1) _
              ≡⟨ β ⟩
            rational (q ℚ.+ ε) ∎

    χ''' : (x : ℝ) → isProp (P x)
    χ''' x = isProp→ (≤-isProp x (rational (q ℚ.+ ε)))

  π : max (rational q) x ∼[ ε , φ ] max (rational q) y
  π = snd maxNonexpandingℝ₂ (rational q) x y ε φ ω

  π' : rational q ∼[ ε , φ ] max (rational q) y
  π' = subst (λ ?x → ?x ∼[ ε , φ ] max (rational q) y)
             (maxCommutative (rational q) x ∙ ψ)
             π

  ρ : max (rational q) y ≤ rational (q ℚ.+ ε)
  ρ = χ φ (≤-reflexive (rational q)) π'

  σ : y ≤ rational (q ℚ.+ ε)
  σ = ≤-transitive
        y (max (rational q) y) (rational (q ℚ.+ ε))
        (≤-max₂ (rational q) y) ρ
  
-- HoTT Lemma 11.3.43(i)
<rational→close→<rational+ε :
  {q : ℚ.ℚ} {x y : ℝ} {ε : ℚ.ℚ}
  (φ : 0 ℚ.< ε) →
  x < rational q →
  x ∼[ ε , φ ] y →
  y < rational (q ℚ.+ ε)
<rational→close→<rational+ε {q} {x} {y} {ε} φ ψ ω =
  ∃-rec (<-isProp y (rational (q ℚ.+ ε))) χ ψ
  where
  χ : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) ×
      (fst u ℚ.< snd u) ×
      (rational (snd u) ≤ rational q) →
      y < rational (q ℚ.+ ε)
  χ (r , s) (π , ρ , σ) =
    ∣ (r ℚ.+ ε , s ℚ.+ ε) , (τ , υ , ο) ∣₁
    where
    τ : y ≤ rational (r ℚ.+ ε)
    τ = ≤rational→close→≤rational+ε φ π ω

    υ : r ℚ.+ ε ℚ.< s ℚ.+ ε
    υ = ℚ.<-+o r s ε ρ

    -- TODO: Use the addition monotone lemma in place of this
    ο : rational (s ℚ.+ ε) ≤ rational (q ℚ.+ ε)
    ο = rationalMonotone {q = s ℚ.+ ε} {r = q ℚ.+ ε}
                         (ℚ.≤-+o s q ε (rationalReflective {q = s} {r = q} σ))
