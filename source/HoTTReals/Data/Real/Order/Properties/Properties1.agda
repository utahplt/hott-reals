module HoTTReals.Data.Real.Order.Properties.Properties1 where

import Cubical.Data.Bool as Bool
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic hiding (⊥; ¬_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary

open BinaryRelation

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Algebra.Negation
open import HoTTReals.Data.Real.Order.Addition.Addition1
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Magnitude
open import HoTTReals.Data.Real.Order.Distance

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

<→∃+ε≤ : {x y : ℝ} → x < y → ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y))
<→∃+ε≤ {x} {y} φ = ∃-rec isPropPropTrunc ψ φ
  where
  ψ : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) × (fst u ℚ.< snd u) × (rational (snd u) ≤ y) →
      ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y))
  ψ (q , r) (χ , ω , π) = ∣ ε , (ρ , ξ) ∣₁
    where
    ε : ℚ.ℚ
    ε = r ℚ.- q

    ρ : 0 ℚ.< ε
    ρ = ℚ.<→0<- {x = q} {y = r} ω

    σ : (q r : ℚ.ℚ) → rational q + rational r ≡ rational (q ℚ.+ r)
    σ = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

    τ : x + rational ε ≤ rational q + rational ε
    τ = addRightMonotone {x = x} {y = rational q} {a = rational ε} χ

    τ' : x + rational ε ≤ rational (q ℚ.+ ε)
    τ' = subst (x + rational ε ≤_) (σ q ε) τ

    υ : q ℚ.+ ε ≡ r
    υ = ℚ.+Comm q ε ∙ ℚ.subtractAddRightCancel q r

    τ'' : x + rational ε ≤ rational r
    τ'' = subst (x + rational ε ≤_) (cong rational υ) τ'

    ξ : x + rational ε ≤ y
    ξ = ≤-transitive (x + rational ε) (rational r) y τ'' π

≤+→-≤ : {x y z : ℝ} → x ≤ y + z → x - z ≤ y
≤+→-≤ {x} {y} {z} φ = ψ'
  where
  ψ : x - z ≤ (y + z) - z
  ψ = addRightMonotone {x = x} {y = y + z} {a = - z} φ

  ψ' : x - z ≤ y
  ψ' = subst (x - z ≤_) (addSubtractRightCancel y z) ψ

+≤→≤- : {x y z : ℝ} → x + y ≤ z → x ≤ z - y
+≤→≤- {x} {y} {z} φ = ψ'
  where
  ψ : (x + y) - y ≤ z - y
  ψ = addRightMonotone {x = x + y} {y = z} {a = - y} φ

  ψ' : x ≤ z - y
  ψ' = subst (_≤ z - y) (addSubtractRightCancel x y) ψ

+≤→≤-' : {x y z : ℝ} → x + y ≤ z → y ≤ z - x
+≤→≤-' {x} {y} {z} φ =
  +≤→≤- {x = y} {y = x} {z = z} φ'
  where
  φ' : y + x ≤ z
  φ' = subst (_≤ z) (+-commutative x y) φ

≤-→+≤ : {x y z : ℝ} → x ≤ z - y → x + y ≤ z
≤-→+≤ {x} {y} {z} φ = ψ'
  where
  ψ : x + y ≤ (z - y) + y
  ψ = addRightMonotone {x = x} {y = z - y} {a = y} φ

  ψ' : x + y ≤ z
  ψ' = subst (x + y ≤_) (subtractAddRightCancel y z) ψ

≤-→+≤' : {x y z : ℝ} → x ≤ z - y → y + x ≤ z
≤-→+≤' {x} {y} {z} φ =
  subst (_≤ z) (+-commutative x y) ψ
  where
  ψ : x + y ≤ z
  ψ = ≤-→+≤ {x = x} {y = y} {z = z} φ

-≤→≤+ : {x y z : ℝ} → x - y ≤ z → x ≤ z + y
-≤→≤+ {x} {y} {z} φ = ψ'
  where
  ψ : (x - y) + y ≤ z + y
  ψ = addRightMonotone {x = x - y} {y = z} {a = y} φ

  ψ' : x ≤ z + y
  ψ' = subst (_≤ z + y) (subtractAddRightCancel y x) ψ

-≤→≤+' : {x y z : ℝ} → x - y ≤ z → x ≤ y + z
-≤→≤+' {x} {y} {z} φ = subst (x ≤_) (+-commutative z y) (-≤→≤+ {x} {y} {z} φ)

close→≤+ε :
  {x y : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x ∼[ ε , φ ] y →
  y ≤ x + rational ε
close→≤+ε {x} {y} {ε} φ ψ = ρ
  where
  ω : - (x - y) ≤ ∣ x - y ∣
  ω = ≤-max₂ (x - y) (- (x - y))

  ω' : y - x ≤ ∣ x - y ∣
  ω' = subst (flip _≤_ ∣ x - y ∣) (negateSubtract' x y) ω 

  χ : ∣ x - y ∣ < rational ε
  χ = close→distance< φ ψ

  χ' : ∣ x - y ∣ ≤ rational ε
  χ' = <→≤ {x = ∣ x - y ∣} {y = rational ε} χ

  π : y - x ≤ rational ε
  π = ≤-transitive (y - x) ∣ x - y ∣ (rational ε) ω' χ'

  ρ : y ≤ x + rational ε
  ρ = -≤→≤+' {x = y} {y = x} {z = rational ε} π

<→close→<+ε :
  {x y z : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x < y →
  x ∼[ ε , φ ] z → 
  z < y + rational ε
<→close→<+ε {x} {y} {z} {ε} φ ψ ω =
  ∃-rec (<-isProp z (y + rational ε)) χ (<-archimedian x y ψ)
  where
  χ : (q : ℚ.ℚ) →
      (x < rational q) × (rational q < y) →
      z < y + rational ε
  χ q (π , ρ) = τ
    where
    σ : z < rational (q ℚ.+ ε)
    σ = <rational→close→<rational+ε φ π ω

    σ' : z < rational q + rational ε
    σ' = subst (z <_) (liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ q ε) σ

    ρ' : rational q + rational ε ≤ y + rational ε
    ρ' = addRightMonotone {x = rational q} {y = y} $
         <→≤ {x = rational q} {y = y} ρ

    τ : z < y + rational ε
    τ = <→≤→< {x = z} {y = rational q + rational ε} {z = y + rational ε} σ' ρ'

<→close→-ε< :
  {x y z : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x < y →
  y ∼[ ε , φ ] z →
  x - rational ε < z
<→close→-ε< {x} {y} {z} {ε} φ ψ ω = σ
  where
  φ' : - y < - x
  φ' = -antitone< {x = x} {y = y} ψ

  ψ' : (- y) ∼[ ε , φ ] (- z)
  ψ' = -nonexpandingℝ y z ε φ ω

  χ : - z < - x + rational ε
  χ = <→close→<+ε {x = - y} {y = - x} {z = - z} φ φ' ψ'

  χ' : - (- x + rational ε) < - (- z)
  χ' = -antitone< {x = - z} {y = - x + rational ε} χ

  π : - (- x + rational ε) ≡ x - rational ε
  π = - (- x + rational ε)
        ≡⟨ negateAdd (- x) (rational ε) ⟩
      - - x + - rational ε
        ≡⟨ cong (flip _+_ (- rational ε)) (-involutive x) ⟩
      x - rational ε ∎

  ρ : - - z ≡ z
  ρ = -involutive z

  σ : x - rational ε < z
  σ = subst2 _<_ π ρ χ'

<-located :
  (q r : ℚ.ℚ) (x : ℝ) →
  q ℚ.< r →
  (rational q < x) ⊔′ (x < rational r)
<-located q r x φ =
  inductionProposition {A = P}
    (rationalCase , limitCase , pIsProp)
    x q r φ
  where
  P : ℝ → Type ℓ-zero
  P x = (q r : ℚ.ℚ) → q ℚ.< r → (rational q < x) ⊔′ (x < rational r)

  rationalCase :
    (s : ℚ.ℚ)
    (q r : ℚ.ℚ) →
    q ℚ.< r →
    (rational q < rational s) ⊔′ (rational s < rational r)
  rationalCase s q r φ = ψ'
    where
    ψ : (q ℚ.< s) ⊔′ (s ℚ.< r)
    ψ = ℚ.isWeaklyLinear< q r s φ

    ψ' : (rational q < rational s) ⊔′ (rational s < rational r)
    ψ' = PropositionalTruncation.map
           (Sum.map (rationalStrictMonotone {q = q} {r = s})
                    (rationalStrictMonotone {q = s} {r = r}))
           ψ

  limitCase :
    (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (φ : CauchyApproximation x) →
    ((ε : ℚ.ℚ) (ψ : 0 ℚ.< ε) →
     (q r : ℚ.ℚ) →
     q ℚ.< r →
     (rational q < x ε ψ) ⊔′ (x ε ψ < rational r)) →
    (q r : ℚ.ℚ) →
    q ℚ.< r →
    (rational q < limit x φ) ⊔′ (limit x φ < rational r)
  limitCase x φ ψ q r ω = ζ
    where
    s : ℚ.ℚ
    s = (1 ℚ.- (1 / 3 [ ℚ.3≠0 ])) ℚ.· q ℚ.+ (1 / 3 [ ℚ.3≠0 ]) ℚ.· r

    t : ℚ.ℚ
    t = (1 ℚ.- (2 / 3 [ ℚ.3≠0 ])) ℚ.· q ℚ.+ (2 / 3 [ ℚ.3≠0 ]) ℚ.· r

    χ : 1 / 3 [ ℚ.3≠0 ] ℚ.< 2 / 3 [ ℚ.3≠0 ]
    χ = Bool.toWitness {Q = ℚ.<Dec (1 / 3 [ ℚ.3≠0 ]) (2 / 3 [ ℚ.3≠0 ])} tt

    χ' : 0 ℚ.< 1 / 3 [ ℚ.3≠0 ]
    χ' = Bool.toWitness {Q = ℚ.<Dec 0 (1 / 3 [ ℚ.3≠0 ])} tt

    χ'' : 2 / 3 [ ℚ.3≠0 ] ℚ.< 1
    χ'' = Bool.toWitness {Q = ℚ.<Dec (2 / 3 [ ℚ.3≠0 ]) 1} tt

    π : q ℚ.< s
    π = ℚ.<→<affineCombination q r (1 / 3 [ ℚ.3≠0 ]) ω χ'

    ρ : s ℚ.< t
    ρ = ℚ.affineCombinationStrictMonotone
          q r (1 / 3 [ ℚ.3≠0 ]) (2 / 3 [ ℚ.3≠0 ]) ω χ

    σ : t ℚ.< r
    σ = ℚ.<→affineCombination< q r (2 / 3 [ ℚ.3≠0 ]) ω χ''

    δ₁ : ℚ.ℚ
    δ₁ = s ℚ.- q

    δ₂ : ℚ.ℚ
    δ₂ = r ℚ.- t

    τ₁ : 0 ℚ.< δ₁
    τ₁ = ℚ.<→0<- {x = q} {y = s} π

    τ₂ : 0 ℚ.< δ₂
    τ₂ = ℚ.<→0<- {x = t} {y = r} σ

    δ : ℚ.ℚ
    δ = (ℚ.min δ₁ δ₂) / 2 [ ℚ.2≠0 ]

    υ : 0 ℚ.< ℚ.min δ₁ δ₂
    υ = ℚ.minGreatestLowerBound< {x = δ₁} {y = δ₂} {z = 0} τ₁ τ₂

    υ' : 0 ℚ.< δ
    υ' = ℚ.0</' {x = ℚ.min δ₁ δ₂} {y = 2} υ ℚ.0<2

    ο : δ ℚ.< ℚ.min δ₁ δ₂
    ο = ℚ.self/2<self (ℚ.min δ₁ δ₂) υ

    ξ₁ : δ ℚ.< δ₁
    ξ₁ = ℚ.isTrans<≤ δ (ℚ.min δ₁ δ₂) δ₁ ο (ℚ.min≤ δ₁ δ₂)

    ξ₂ : δ ℚ.< δ₂
    ξ₂ = ℚ.isTrans<≤ δ (ℚ.min δ₁ δ₂) δ₂ ο (ℚ.min≤' δ₁ δ₂)

    α : (rational s < x δ υ') ⊔′ (x δ υ' < rational t)
    α = ψ δ υ' s t ρ

    β : rational s < x δ υ' → rational q < limit x φ
    β ζ = μ'
      where
      ξ₁' : 0 ℚ.< δ₁ ℚ.- δ
      ξ₁' = ℚ.<→0<- {x = δ} {y = δ₁} ξ₁

      ι : x δ υ' ∼[ (δ₁ ℚ.- δ) ℚ.+ δ , ℚ.0<+' {x = δ₁ ℚ.- δ} {y = δ} ξ₁' υ' ]
          limit x φ
      ι = closeLimit'' x φ δ (δ₁ ℚ.- δ) υ' ξ₁'

      κ : (δ₁ ℚ.- δ) ℚ.+ δ ≡ δ₁
      κ = ℚ.subtractAddRightCancel δ δ₁

      ι' : Σ (0 ℚ.< δ₁) (λ ξ → Close δ₁ ξ (x δ υ') (limit x φ))
      ι' = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ (x δ υ') (limit x φ)))
                 κ
                 (_ , ι)

      ι'' : Close δ₁ (fst ι') (limit x φ) (x δ υ')
      ι'' = closeSymmetric (x δ υ') (limit x φ) δ₁ (fst ι') (snd ι')

      μ : rational s - rational δ₁ < limit x φ
      μ = <→close→-ε< {x = rational s} {y = x δ υ'} {z = limit x φ}
                      (fst ι') ζ (snd ι')

      ν : rational s - rational δ₁ ≡ rational q
      ν = cong rational (ℚ.leftSubtractSubtractCancel s q)

      μ' : rational q < limit x φ
      μ' = subst (_< limit x φ) ν μ

    γ : x δ υ' < rational t → limit x φ < rational r
    γ ζ = μ'
      where
      ξ₂' : 0 ℚ.< δ₂ ℚ.- δ
      ξ₂' = ℚ.<→0<- {x = δ} {y = δ₂} ξ₂

      ι : x δ υ' ∼[ (δ₂ ℚ.- δ) ℚ.+ δ , ℚ.0<+' {x = δ₂ ℚ.- δ} {y = δ} ξ₂' υ' ]
          limit x φ
      ι = closeLimit'' x φ δ (δ₂ ℚ.- δ) υ' ξ₂'

      κ : (δ₂ ℚ.- δ) ℚ.+ δ ≡ δ₂
      κ = ℚ.subtractAddRightCancel δ δ₂

      ι' : Σ (0 ℚ.< δ₂) (λ ξ → Close δ₂ ξ (x δ υ') (limit x φ))
      ι' = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ (x δ υ') (limit x φ)))
                 κ
                 (_ , ι)

      μ : limit x φ < rational t + rational δ₂
      μ = <→close→<+ε {x = x δ υ'} {y = rational t} {z = limit x φ}
                      (fst ι') ζ (snd ι')

      ν : rational t + rational δ₂ ≡ rational r
      ν = rational t + rational δ₂
            ≡⟨ liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ t δ₂ ⟩
          rational (t ℚ.+ δ₂)
            ≡⟨ cong rational (ℚ.+Comm t δ₂) ⟩
          rational (δ₂ ℚ.+ t)
            ≡⟨ cong rational (ℚ.subtractAddRightCancel t r) ⟩
          rational r ∎

      μ' : limit x φ < rational r
      μ' = subst (_<_ $ limit x φ) ν μ

    ζ : (rational q < limit x φ) ⊔′ (limit x φ < rational r)
    ζ = PropositionalTruncation.map (Sum.map β γ) α

  pIsProp : (x : ℝ) → isProp $ P x
  pIsProp x = isPropΠ3 (λ q r φ → isPropPropTrunc)

<-isWeaklyLinear : isWeaklyLinear _<_
<-isWeaklyLinear x y z = ∃-rec isPropPropTrunc φ 
  where
  φ : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) × ((fst u) ℚ.< (snd u)) × (rational (snd u) ≤ y) →
      (x < z) ⊔′ (z < y)
  φ (q , r) (ψ , ω , χ) = ρ
    where
    π : (rational q < z) ⊔′ (z < rational r)
    π = <-located q r z ω

    ρ : (x < z) ⊔′ (z < y)
    ρ = PropositionalTruncation.map
          (Sum.map (≤→<→< {x = x} ψ) (flip (<→≤→< {x = z}) χ))
          π

isStrictOrder< : IsStrictOrder _<_
isStrictOrder< =
  isstrictorder
    ℝ-isSet
    <-isProp
    <-irreflexive
    <-transitive
    (isIrrefl×isTrans→isAsym _<_ (<-irreflexive , <-transitive))
    <-isWeaklyLinear

_#_ : ℝ → ℝ → Type ℓ-zero
_#_ = SymClosure _<_

infix 4 _#_ 

isApartness# : IsApartness _#_
isApartness# = isStrictOrder→isApartnessSymClosure isStrictOrder<

#-isProp : isPropValued _#_
#-isProp = IsApartness.is-prop-valued isApartness#

#-irreflexive : isIrrefl _#_
#-irreflexive = IsApartness.is-irrefl isApartness#

#-cotransitive : isCotrans _#_
#-cotransitive = IsApartness.is-cotrans isApartness#

#-symmetric : isSym _#_
#-symmetric = IsApartness.is-sym isApartness#

apart→negateApart : {x : ℝ} → x # 0 → (- x) # 0
apart→negateApart {x} (inl φ) = inr $ -antitone< {x} {0} φ
apart→negateApart {x} (inr φ) = inl $ -antitone< {0} {x} φ

negateApart→apart : {x : ℝ} → (- x) # 0 → x # 0
negateApart→apart {x} (inl φ) = inr ψ'
  where
  ψ : 0 < - - x
  ψ = -antitone< { - x } {0} φ

  ψ' : 0 < x
  ψ' = subst (_<_ 0) (-involutive x) ψ
negateApart→apart {x} (inr φ) = inl ψ'
  where
  ψ : - - x < 0
  ψ = -antitone< {0} { - x } φ

  ψ' : x < 0
  ψ' = subst (flip _<_ 0) (-involutive x) ψ

<+ε : (x : ℝ) (ε : ℚ.ℚ) →
      0 ℚ.< ε →
      x < x + rational ε
<+ε =
  inductionProposition {A = P} (rationalCase , limitCase , pIsProp)
  where
  P : ℝ → Type ℓ-zero
  P x = (ε : ℚ.ℚ) → 0 ℚ.< ε → x < x + rational ε

  rationalCase :
    (q : ℚ.ℚ) (ε : ℚ.ℚ) →
    0 ℚ.< ε →
    rational q < rational q + rational ε
  rationalCase q ε φ = ψ''
    where
    ψ : q ℚ.+ 0 ℚ.< q ℚ.+ ε
    ψ = ℚ.<-o+ 0 ε q φ

    ψ' : q ℚ.< q ℚ.+ ε
    ψ' = subst (flip ℚ._<_ $ q ℚ.+ ε) (ℚ.+IdR q) ψ

    ψ'' : rational q < rational q + rational ε
    ψ'' = rationalStrictMonotone {q = q} {r = q ℚ.+ ε} ψ'

  limitCase :
    (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (φ : CauchyApproximation x) →
    ((ε : ℚ.ℚ) (ψ : 0 ℚ.< ε)
     (δ : ℚ.ℚ) → 0 ℚ.< δ →
     x ε ψ < x ε ψ + rational δ) →
    (ε : ℚ.ℚ) → 0 ℚ.< ε →
    limit x φ < limit x φ + rational ε
  limitCase x φ ψ ε ω = ο
    where
    δ : ℚ.ℚ
    δ = ε / 5 [ ℚ.5≠0 ]

    χ : 0 ℚ.< δ
    χ = ℚ.0</' {x = ε} {y = 5} ω ℚ.0<5

    π : x δ χ < x δ χ + rational δ
    π = ψ δ χ δ χ

    ρ : x δ χ ∼[ δ ℚ.+ δ , ℚ.0<+' {x = δ} {y = δ} χ χ ] limit x φ
    ρ = closeLimit'' x φ δ δ χ χ

    σ : limit x φ < (x δ χ + rational δ) + rational (δ ℚ.+ δ)
    σ = <→close→<+ε {x = x δ χ} {y = x δ χ + rational δ} {z = limit x φ}
                    (ℚ.0<+' {x = δ} {y = δ} χ χ) π ρ

    τ : (limit x φ < limit x φ + rational ε) ⊔′
        (limit x φ + rational ε < (x δ χ + rational δ) + rational (δ ℚ.+ δ))
    τ = <-isWeaklyLinear
         (limit x φ)
         ((x δ χ + rational δ) + rational (δ ℚ.+ δ))
         (limit x φ + rational ε)
         σ

    υ : ¬ (limit x φ + rational ε < (x δ χ + rational δ) + rational (δ ℚ.+ δ))
    υ ξ = κ
      where
      ο : (x δ χ + rational δ) + rational (δ ℚ.+ δ) ≡
          x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)
      ο = (x δ χ + rational δ) + rational (δ ℚ.+ δ)
            ≡⟨ +-associative (x δ χ) (rational δ) (rational (δ ℚ.+ δ)) ⟩
          x δ χ + rational (δ ℚ.+ (δ ℚ.+ δ))
            ≡⟨ cong (λ ?x → (x δ χ) + rational ?x) (ℚ.+Assoc δ δ δ) ⟩
          x δ χ + rational ((δ ℚ.+ δ) ℚ.+ δ) ∎

      ξ' : limit x φ + rational ε < x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)
      ξ' = subst (_<_ $ limit x φ + rational ε) ο ξ

      ρ' : limit x φ ∼[ δ ℚ.+ δ , ℚ.0<+' {x = δ} {y = δ} χ χ ] x δ χ 
      ρ' = closeSymmetric (x δ χ) (limit x φ) (δ ℚ.+ δ) _ ρ

      α : x δ χ ≤ limit x φ + rational (δ ℚ.+ δ)
      α = close→≤+ε {x = limit x φ} {y = x δ χ} _ ρ'

      β : x δ χ + rational (δ ℚ.+ δ ℚ.+ δ) ≤
          (limit x φ + rational (δ ℚ.+ δ)) + rational (δ ℚ.+ δ ℚ.+ δ)
      β = addRightMonotone {x = x δ χ} α

      -- TODO: Replace
      γ : ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ ℚ.+ δ)) ≡ ε
      γ = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ ℚ.+ δ)
            ≡⟨ cong₂ ℚ._+_ (ℚ.self+≡2· δ)
                     (cong (flip ℚ._+_ δ) (ℚ.self+≡2· δ)) ⟩
          2 ℚ.· δ ℚ.+ (2 ℚ.· δ ℚ.+ δ)
            ≡⟨ cong (λ ?x → 2 ℚ.· δ ℚ.+ (2 ℚ.· δ ℚ.+ ?x))
                    (sym (ℚ.·IdL δ)) ⟩
          2 ℚ.· δ ℚ.+ (2 ℚ.· δ ℚ.+ 1 ℚ.· δ)
            ≡⟨ cong (ℚ._+_ (2 ℚ.· δ)) (sym (ℚ.·DistR+ 2 1 δ)) ⟩
          2 ℚ.· δ ℚ.+ 3 ℚ.· δ
            ≡⟨ sym (ℚ.·DistR+ 2 3 δ) ⟩
          5 ℚ.· δ
            ≡⟨ ℚ.·/ ε 5 ℚ.5≠0 ⟩
          ε ∎

      ζ : (limit x φ + rational (δ ℚ.+ δ)) + rational (δ ℚ.+ δ ℚ.+ δ) ≡
          limit x φ + rational ε
      ζ = (limit x φ + rational (δ ℚ.+ δ)) + rational (δ ℚ.+ δ ℚ.+ δ)
            ≡⟨ +-associative (limit x φ)
                             (rational (δ ℚ.+ δ))
                             (rational (δ ℚ.+ δ ℚ.+ δ)) ⟩
          limit x φ + rational ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ ℚ.+ δ))
            ≡⟨ cong (λ ?x → (limit x φ) + rational ?x) γ ⟩
          limit x φ + rational ε ∎

      β' : x δ χ + rational (δ ℚ.+ δ ℚ.+ δ) ≤
           limit x φ + rational ε
      β' = subst (_≤_ $ x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)) ζ β

      ι : x δ χ + rational (δ ℚ.+ δ ℚ.+ δ) < x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)
      ι = ≤→<→< {x = x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)}
                {y = limit x φ + rational ε}
                β' ξ'

      κ : ⊥
      κ = <-irreflexive (x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)) ι

    ο : limit x φ < limit x φ + rational ε
    ο = PropositionalTruncation.rec
          (<-isProp (limit x φ) (limit x φ + rational ε))
          (Sum.rec (idfun _) (Empty.rec ∘ υ))
          τ

  pIsProp : (x : ℝ) → isProp (P x)
  pIsProp x = isPropΠ2 (λ ε φ → <-isProp x (x + rational ε))

+ε≤→< :
  {x y : ℝ} {ε : ℚ.ℚ} →
  0 ℚ.< ε →
  x + rational ε ≤ y →
  x < y
+ε≤→< {x} {y} {ε} φ ψ = χ
  where
  ω : x < x + rational ε
  ω = <+ε x ε φ

  χ : x < y
  χ = <→≤→< {x = x} {y = x + rational ε} {z = y} ω ψ

∃+ε≤→< :
  {x y : ℝ} →
  ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y)) →
  x < y
∃+ε≤→< {x} {y} φ = ∃-rec (<-isProp x y) ψ φ
  where
  ψ : (ε : ℚ.ℚ) → (0 ℚ.< ε) × (x + rational ε ≤ y) → x < y
  ψ ε (ω , χ) = +ε≤→< {x = x} {y = y} {ε = ε} ω χ

<↔∃+ε≤ : {x y : ℝ} → (x < y) ↔ ∃ ℚ.ℚ (λ ε → (0 ℚ.< ε) × (x + rational ε ≤ y))
<↔∃+ε≤ {x} {y} = ( <→∃+ε≤ {x = x} {y = y} , ∃+ε≤→< {x = x} {y = y} )
