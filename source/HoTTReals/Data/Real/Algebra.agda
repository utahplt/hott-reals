module HoTTReals.Data.Real.Algebra where

import Cubical.Data.Bool as Bool
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PropositionalTruncation
open import Cubical.Homotopy.Base
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order

open BinaryRelation

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

instance
  fromNatℝ : HasFromNat ℝ
  fromNatℝ = record
    { Constraint = λ _ → Unit ;
      fromNat = λ n → rational $ fromNat n }

instance
  fromNegℝ : HasFromNeg ℝ
  fromNegℝ = record
    { Constraint = λ _ → Unit ;
      fromNeg = λ n → rational $ fromNat n }

-lipschitzℚ : Lipschitzℚ (rational ∘ ℚ.-_) 1 0<1
-lipschitzℚ q r ε φ ψ =
  rationalRational
    (ℚ.- q) (ℚ.- r)
    (1 ℚ.· ε) (0<· {x = 1} {y = ε} 0<1 φ)
    (∣∣<→<₂ {x = (ℚ.- q) ℚ.- (ℚ.- r)} {ε = 1 ℚ.· ε} χ)
    (∣∣<→<₁ {x = (ℚ.- q) ℚ.- (ℚ.- r)} {ε = 1 ℚ.· ε} χ)
  where
  ω : ∣ (ℚ.- q) ℚ.- (ℚ.- r) ∣ ≡ ∣ q ℚ.- r ∣
  ω = -distance q r

  χ : ∣ (ℚ.- q) ℚ.- (ℚ.- r) ∣ ℚ.< 1 ℚ.· ε
  χ = subst2 ℚ._<_ (sym ω) (sym $ ℚ.·IdL ε) ψ

-_ : ℝ → ℝ
-_ = liftLipschitz (rational ∘ ℚ.-_) 1 0<1 -lipschitzℚ

infix  8 -_

-lipschitzℝ : Lipschitzℝ -_ 1 0<1
-lipschitzℝ =
  -- The Agda type checker is weird, why do you freeze if I just put this
  -- directly but you finish instantly if I put this in a let block without an
  -- explicit type and then immediately return it?
  let φ = liftLipschitzLipschitz (rational ∘ ℚ.-_) 1 0<1 -lipschitzℚ
  in φ

-continuous : Continuous -_
-continuous = lipschitz→continuous -_ 1 0<1 -lipschitzℝ

+nonexpandingℚ₂ : Nonexpandingℚ₂ ℚ._+_
+nonexpandingℚ₂ =
  φ , ψ
  where
  φ : (q r s : ℚ.ℚ) → distance (q ℚ.+ s) (r ℚ.+ s) ℚ.≤ distance q r
  φ q r s =
    ℚ.≡Weaken≤ (distance (q ℚ.+ s) (r ℚ.+ s)) (distance q r) (+distanceᵣ q r s)

  ψ : (q r s : ℚ.ℚ) → distance (q ℚ.+ r) (q ℚ.+ s) ℚ.≤ distance r s
  ψ q r s =
    ℚ.≡Weaken≤ (distance (q ℚ.+ r) (q ℚ.+ s)) (distance r s) (+distanceₗ q r s)

_+_ : ℝ → ℝ → ℝ
_+_ = liftNonexpanding₂ ℚ._+_ +nonexpandingℚ₂

infixl 6 _+_

+nonexpandingℝ₂ : Nonexpandingℝ₂ _+_
+nonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ._+_ +nonexpandingℚ₂

+lipschitz₁ : (v : ℝ) → Lipschitzℝ (flip _+_ v) 1 0<1
+lipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ _+_ +nonexpandingℝ₂

+lipschitz₂ : (u : ℝ) → Lipschitzℝ (_+_ u) 1 0<1
+lipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ _+_ +nonexpandingℝ₂

+continuous₁ : (v : ℝ) → Continuous (flip _+_ v)
+continuous₁ v = lipschitz→continuous (flip _+_ v) 1 0<1 (+lipschitz₁ v)

+continuous₂ : (u : ℝ) → Continuous (_+_ u)
+continuous₂ u = lipschitz→continuous (_+_ u) 1 0<1 (+lipschitz₂ u)

-- Need this lame lemma for additive inverse law below. There are many other
-- lemmas I could've proved, but this is the one that seemed easiest to me which
-- was sufficient
-+lipschitz : Lipschitzℝ (λ u → - u + u) 2 0<2
-+lipschitz u v ε φ ψ = ρ''
  where
  ω : Close (1 ℚ.· ε) (0<· {x = 1} {y = ε} 0<1 φ) (- u) (- v)
  ω = -lipschitzℝ u v ε φ ψ

  ω' : Σ (0 ℚ.< ε) (λ ω → Close ε ω (- u) (- v))
  ω' = subst (λ ?x → Σ (0 ℚ.< ?x) λ ω → Close ?x ω (- u) (- v))
             (ℚ.·IdL ε)
             ((0<· {x = 1} {y = ε} 0<1 φ) , ω)

  ω'' : Close ε φ (- u) (- v)
  ω'' = subst (λ ?x → Close ε ?x (- u) (- v))
              (ℚ.isProp< 0 ε (fst ω') φ)
              (snd ω')

  χ : Close ε φ (- u + v) (- v + v)
  χ = fst +nonexpandingℝ₂ (- u) (- v) v ε φ ω''

  π : Close ε φ (- u + u) (- u + v)
  π = snd +nonexpandingℝ₂ (- u) u v ε φ ψ

  ρ : Close (ε ℚ.+ ε) (0<+' {x = ε} {y = ε} φ φ) (- u + u) (- v + v)
  ρ = closeTriangleInequality (- u + u) (- u + v) (- v + v)
                              ε ε φ φ π χ

  ρ' : Σ (0 ℚ.< 2 ℚ.· ε) (λ ω → Close (2 ℚ.· ε) ω (- u + u) (- v + v))
  ρ' = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ω → Close ?x ω _ _))
             (self+≡2· ε)
             ((0<+' {x = ε} {y = ε} φ φ) , ρ)

  ρ'' : Close (2 ℚ.· ε) (0<· {x = 2} {y = ε} 0<2 φ) (- u + u) (- v + v)
  ρ'' = subst (λ ?x → Close (2 ℚ.· ε) ?x (- u + u) (- v + v))
              (ℚ.isProp< 0 (2 ℚ.· ε)
                         (fst ρ') (0<· {x = 2} {y = ε} 0<2 φ))
              (snd ρ')

_-_ : ℝ → ℝ → ℝ
_-_ x y = x + (- y)

infixl 6 _-_

-- TODO: Abelian group structure
-- TODO: Figure out whether we get a total order for the reals or not

+-commutative : (x y : ℝ) → x + y ≡ y + x
+-commutative =
  continuousExtensionLaw₂
    _+_ (flip _+_) ℚ._+_ (flip ℚ._+_)
    φ
    (flip φ)
    ψ ω χ χ ω
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ._+_ +nonexpandingℚ₂ (rational q) (rational r) ≡
      rational (q ℚ.+ r)
  φ = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

  ψ : (x y : ℚ.ℚ) → x ℚ.+ y ≡ y ℚ.+ x
  ψ = ℚ.+Comm

  ω : (u : ℝ) → Continuous (_+_ u)
  ω = +continuous₂

  χ : (v : ℝ) → Continuous $ flip _+_ v
  χ = +continuous₁

+-associative : (x y z : ℝ) → (x + y) + z ≡ x + (y + z)
+-associative =
  continuousExtensionLaw₃
    associateℝₗ
    associateℝᵣ
    associateℚₗ
    associateℚᵣ
    ψ ω χ π ρ σ τ υ ξ
  where
  associateℝₗ : ℝ → ℝ → ℝ → ℝ
  associateℝₗ x y z = (x + y) + z

  associateℝᵣ : ℝ → ℝ → ℝ → ℝ
  associateℝᵣ x y z = x + (y + z)

  associateℚₗ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚₗ x y z = (x ℚ.+ y) ℚ.+ z

  associateℚᵣ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚᵣ x y z = x ℚ.+ (y ℚ.+ z)

  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ._+_ +nonexpandingℚ₂ (rational q) (rational r) ≡
      rational (q ℚ.+ r)
  φ = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ 

  ψ : (q r s : ℚ.ℚ) →
      associateℝₗ (rational q) (rational r) (rational s) ≡
      rational (associateℚₗ q r s)
  ψ q r s =
    (rational q + rational r) + rational s
      ≡⟨ cong (flip _+_ $ rational s) (φ q r) ⟩
    rational (q ℚ.+ r) + rational s
      ≡⟨ φ (q ℚ.+ r) s ⟩
    rational ((q ℚ.+ r) ℚ.+ s) ∎

  ω : (q r s : ℚ.ℚ) →
      associateℝᵣ (rational q) (rational r) (rational s) ≡
      rational (associateℚᵣ q r s)
  ω q r s =
    rational q + (rational r + rational s)
      ≡⟨ cong (_+_ $ rational q) (φ r s) ⟩
    rational q + rational (r ℚ.+ s)
      ≡⟨ φ q (r ℚ.+ s) ⟩
    rational (q ℚ.+ (r ℚ.+ s)) ∎

  χ : (q r s : ℚ.ℚ) → associateℚₗ q r s ≡ associateℚᵣ q r s
  χ q r s = sym $ ℚ.+Assoc q r s

  π : (x y : ℝ) → Continuous (associateℝₗ x y)
  π x y = +continuous₂ (x + y)

  ρ : (x z : ℝ) → Continuous (λ y → associateℝₗ x y z)
  ρ x z = continuousCompose (_+_ x) (flip _+_ z)
                            (+continuous₂ x) (+continuous₁ z)

  σ : (y z : ℝ) → Continuous (λ x → associateℝₗ x y z)
  σ y z = continuousCompose (flip _+_ y) (flip _+_ z)
                            (+continuous₁ y) (+continuous₁ z)

  τ : (x y : ℝ) → Continuous (associateℝᵣ x y)
  τ x y = continuousCompose (_+_ y) (_+_ x)
                            (+continuous₂ y) (+continuous₂ x)

  υ : (x z : ℝ) → Continuous (λ y → associateℝᵣ x y z)
  υ x z = continuousCompose (flip _+_ z) (_+_ x)
                            (+continuous₁ z) (+continuous₂ x)

  ξ : (y z : ℝ) → Continuous (λ x → associateℝᵣ x y z)
  ξ y z = +continuous₁ (y + z)

+-associative' : (x y z : ℝ) → x + (y + z) ≡ (x + y) + z
+-associative' x y z = sym $ +-associative x y z

+-unitˡ : (x : ℝ) → 0 + x ≡ x
+-unitˡ =
  continuousExtensionLaw₁
    (_+_ 0) (idfun ℝ)
    (ℚ._+_ 0) (idfun ℚ.ℚ)
    H K L φ ψ
  where
  H : (_+_ 0 ∘ rational) ∼ (rational ∘ ℚ._+_ 0)
  H = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ 0

  K : (idfun ℝ ∘ rational) ∼ (rational ∘ idfun ℚ.ℚ)
  K q = refl

  L : ℚ._+_ 0 ∼ idfun ℚ.ℚ
  L = ℚ.+IdL

  φ : Continuous (_+_ 0)
  φ = +continuous₂ 0

  ψ : Continuous (idfun ℝ)
  ψ = identityContinuous

+-unitʳ : (x : ℝ) → x + 0 ≡ x
+-unitʳ x =
  x + 0
    ≡⟨ +-commutative x 0 ⟩
  0 + x
    ≡⟨ +-unitˡ x ⟩
  x ∎

+-inverseₗ : (x : ℝ) → (- x) + x ≡ 0
+-inverseₗ =
  continuousExtensionLaw₁
    (λ x → (- x) + x) (const 0)
    (λ x → (ℚ.- x) ℚ.+ x) (const 0)
    φ ψ ω χ π
  where
  φ : (q : ℚ.ℚ) → - rational q + rational q ≡ rational (ℚ.- q ℚ.+ q)
  φ q =
    - rational q + rational q
      ≡⟨ cong (flip _+_ $ rational q)
              (liftLipschitz≡rational (rational ∘ ℚ.-_) 1 0<1 -lipschitzℚ q) ⟩
    rational (ℚ.- q) + rational q
      ≡⟨ liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ (ℚ.- q) q ⟩
    rational (ℚ.- q ℚ.+ q) ∎

  ψ : (q : ℚ.ℚ) → ((λ _ → 0) ∘ rational) q ≡ (rational ∘ (λ _ → 0)) q
  ψ q = refl

  ω : (q : ℚ.ℚ) → (ℚ.- q) ℚ.+ q ≡ 0
  ω = ℚ.+InvL

  χ : Continuous (λ x → - x + x)
  χ = lipschitz→continuous (λ x → - x + x) 2 0<2 -+lipschitz

  π : Continuous $ const 0
  π = constantContinuous 0

+-inverseᵣ : (x : ℝ) → x + (- x) ≡ 0
+-inverseᵣ x =
  x + (- x)
    ≡⟨ +-commutative x (- x) ⟩
  (- x) + x
    ≡⟨ +-inverseₗ x ⟩
  0 ∎

isAbelianGroupℝ : IsAbGroup 0 _+_ (-_)
isAbelianGroupℝ =
  makeIsAbGroup
    ℝ-isSet
    +-associative'
    +-unitʳ
    +-inverseᵣ
    +-commutative

ℝ+ : AbGroup ℓ-zero
ℝ+ = ℝ , (abgroupstr 0 _+_ -_ isAbelianGroupℝ)

maxNonexpandingℚ₂ : Nonexpandingℚ₂ ℚ.max
maxNonexpandingℚ₂ = φ , ψ
  where
  φ : (q r s : ℚ.ℚ) → distance (ℚ.max q s) (ℚ.max r s) ℚ.≤ distance q r
  φ = maxNonexpandingˡ

  ψ : (q r s : ℚ.ℚ) → distance (ℚ.max q r) (ℚ.max q s) ℚ.≤ distance r s
  ψ = maxNonexpandingʳ

max : ℝ → ℝ → ℝ
max = liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂

maxNonexpandingℝ₂ : Nonexpandingℝ₂ max
maxNonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ.max maxNonexpandingℚ₂

maxLipschitz₁ : (v : ℝ) → Lipschitzℝ (flip max v) 1 0<1
maxLipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ max maxNonexpandingℝ₂

maxLipschitz₂ : (u : ℝ) → Lipschitzℝ (max u) 1 0<1
maxLipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ max maxNonexpandingℝ₂

maxContinuous₁ : (v : ℝ) → Continuous (flip max v)
maxContinuous₁ v = lipschitz→continuous (flip max v) 1 0<1 (maxLipschitz₁ v)

maxContinuous₂ : (u : ℝ) → Continuous (max u)
maxContinuous₂ u = lipschitz→continuous (max u) 1 0<1 (maxLipschitz₂ u)

-- Same deal as x + (- x), see comment above
maxMaxLipschitz : Lipschitzℝ (λ u → max u u) 2 0<2
maxMaxLipschitz u v ε φ ψ = π''
  where
  ω : Close ε φ (max u u) (max u v)
  ω = snd maxNonexpandingℝ₂ u u v ε φ ψ

  χ : Close ε φ (max u v) (max v v)
  χ = fst maxNonexpandingℝ₂ u v v ε φ ψ

  π : Close (ε ℚ.+ ε) (0<+' {x = ε} {y = ε} φ φ) (max u u) (max v v)
  π = closeTriangleInequality (max u u) (max u v) (max v v)
                              ε ε φ φ ω χ

  π' : Σ (0 ℚ.< 2 ℚ.· ε) (λ ξ → Close (2 ℚ.· ε) ξ (max u u) (max v v))
  π' = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ _ _))
             (self+≡2· ε)
             ((0<+' {x = ε} {y = ε} φ φ) , π)

  π'' : Close (2 ℚ.· ε) (0<· {x = 2} {y = ε} 0<2 φ) (max u u) (max v v)
  π'' = subst (λ ?x → Close (2 ℚ.· ε) ?x (max u u) (max v v))
              (ℚ.isProp< 0 (2 ℚ.· ε)
                         (fst π') (0<· {x = 2} {y = ε} 0<2 φ))
              (snd π')

maxAssociative : (x y z : ℝ) → max (max x y) z ≡ max x (max y z)
maxAssociative =
  continuousExtensionLaw₃
    associateℝₗ associateℝᵣ associateℚₗ associateℚᵣ
    ψ ω χ π ρ σ τ υ ξ
  where
  associateℝₗ : ℝ → ℝ → ℝ → ℝ
  associateℝₗ x y z = max (max x y) z

  associateℝᵣ : ℝ → ℝ → ℝ → ℝ
  associateℝᵣ x y z = max x (max y z)

  associateℚₗ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚₗ q r s = ℚ.max (ℚ.max q r) s

  associateℚᵣ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚᵣ q r s = ℚ.max q (ℚ.max r s)

  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.max q r)
  φ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 

  ψ : (q r s : ℚ.ℚ) →
      associateℝₗ (rational q) (rational r) (rational s) ≡
      rational (associateℚₗ q r s)
  ψ q r s =
    max (max (rational q) (rational r)) (rational s)
      ≡⟨ cong (flip max $ rational s) (φ q r) ⟩
    max (rational (ℚ.max q r)) (rational s)
      ≡⟨ φ (ℚ.max q r) s ⟩
    rational (ℚ.max (ℚ.max q r) s) ∎

  ω : (q r s : ℚ.ℚ) →
      associateℝᵣ (rational q) (rational r) (rational s) ≡
      rational (associateℚᵣ q r s)
  ω q r s =
    max (rational q) (max (rational r) (rational s))
      ≡⟨ cong (max $ rational q) (φ r s) ⟩
    max (rational q) (rational (ℚ.max r s))
      ≡⟨ φ q (ℚ.max r s) ⟩
    rational (ℚ.max q (ℚ.max r s)) ∎

  χ : (q r s : ℚ.ℚ) → associateℚₗ q r s ≡ associateℚᵣ q r s
  χ q r s = sym $ ℚ.maxAssoc q r s

  π : (x y : ℝ) → Continuous (associateℝₗ x y)
  π x y = maxContinuous₂ (max x y)

  ρ : (x z : ℝ) → Continuous (λ y → associateℝₗ x y z)
  ρ x z = continuousCompose (max x) (flip max z)
                            (maxContinuous₂ x) (maxContinuous₁ z)

  σ : (y z : ℝ) → Continuous (λ x → associateℝₗ x y z)
  σ y z = continuousCompose (flip max y) (flip max z)
                            (maxContinuous₁ y) (maxContinuous₁ z)

  τ : (x y : ℝ) → Continuous (associateℝᵣ x y)
  τ x y = continuousCompose (max y) (max x)
                            (maxContinuous₂ y) (maxContinuous₂ x)

  υ : (x z : ℝ) → Continuous (λ y → associateℝᵣ x y z)
  υ x z = continuousCompose (flip max z) (max x)
                            (maxContinuous₁ z) (maxContinuous₂ x)

  ξ : (y z : ℝ) → Continuous (λ x → associateℝᵣ x y z)
  ξ y z = maxContinuous₁ (max y z)

maxCommutative : (x y : ℝ) → max x y ≡ max y x
maxCommutative =
  continuousExtensionLaw₂
    max
    (flip max)
    ℚ.max
    (flip ℚ.max)
    φ (flip φ) ψ ω χ χ ω
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.max q r)
  φ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 

  ψ : (x y : ℚ.ℚ) → ℚ.max x y ≡ ℚ.max y x
  ψ = ℚ.maxComm

  ω : (u : ℝ) → Continuous (max u)
  ω = maxContinuous₂

  χ : (v : ℝ) → Continuous $ flip max v
  χ = maxContinuous₁

maxIdempotent : (x : ℝ) → max x x ≡ x
maxIdempotent =
  continuousExtensionLaw₁
    (λ x → max x x) (idfun ℝ)
    (λ q → ℚ.max q q) (idfun ℚ.ℚ)
    ψ ω χ π ρ
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.max q r)
  φ = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 

  ψ : ((λ x → max x x) ∘ rational) ∼ (rational ∘ (λ q → ℚ.max q q))
  ψ q = φ q q

  ω : (idfun ℝ ∘ rational) ∼ (rational ∘ idfun ℚ.ℚ)
  ω q = refl

  χ : (λ q → ℚ.max q q) ∼ idfun ℚ.ℚ
  χ = ℚ.maxIdem

  π : Continuous (λ x → max x x)
  π = lipschitz→continuous (λ x → max x x) 2 0<2 maxMaxLipschitz
  
  ρ : Continuous (idfun ℝ)
  ρ = identityContinuous

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
  π = ≡max→≤₂ {x = q} {y = r} χ

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
    m = (q ℚ.+ r) / 2 [ 2≠0 ]

    ρ : x < rational m
    ρ = ∣ (q , m) ,
          (ω ,
           (<→<-midpoint {x = q} {y = r} χ) ,
           (≤-reflexive $ rational m)) ∣₁

    σ : rational m < y
    σ = ∣ (m , r) ,
          ((≤-reflexive $ rational m) ,
           (<→midpoint-< {x = q} {y = r} χ) ,
           π) ∣₁

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
      π' : ∣ r ℚ.- s ∣ ℚ.< ε
      π' = close→close' (rational r) (rational s) ε φ π

      ρ : s ℚ.- r ℚ.≤ ∣ r ℚ.- s ∣
      ρ = subst (flip ℚ._≤_ ∣ r ℚ.- s ∣)
                (negateSubtract' r s)
                (≤max' (r ℚ.- s) (ℚ.- (r ℚ.- s)))

      σ : r ℚ.+ (s ℚ.- r) ℚ.≤ r ℚ.+ ∣ r ℚ.- s ∣
      σ = ℚ.≤-o+ (s ℚ.- r) ∣ r ℚ.- s ∣ r ρ

      σ' : s ℚ.≤ r ℚ.+ ∣ r ℚ.- s ∣
      σ' = subst (flip ℚ._≤_ $ r ℚ.+ ∣ r ℚ.- s ∣)
                 (addLeftSubtractCancel r s)
                 σ

      τ : r ℚ.+ ∣ r ℚ.- s ∣ ℚ.≤ q ℚ.+ ε
      τ = +≤+ {x = r} {y = q} {z = ∣ r ℚ.- s ∣} {w = ε}
              (rationalReflective {q = r} {r = q} ψ)
              (ℚ.<Weaken≤ ∣ r ℚ.- s ∣ ε π')

      υ : s ℚ.≤ q ℚ.+ ε
      υ = ℚ.isTrans≤ s (r ℚ.+ ∣ r ℚ.- s ∣) (q ℚ.+ ε) σ' τ

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
          α = 0<+' {x = θ ℚ.- δ} {y = δ} (<→0<- {x = δ} {y = θ} ο) ξ

          β : limit x ω ∼[ (θ ℚ.- δ) ℚ.+ δ , α ] x δ ξ
          β = limitClose'' x ω δ (θ ℚ.- δ) ξ (<→0<- {x = δ} {y = θ} ο)

          γ  : rational r ∼[ (ε ℚ.- θ) ℚ.+ ((θ ℚ.- δ) ℚ.+ δ) ,
                             0<+' {x = ε ℚ.- θ} τ α ]
               x δ ξ
          γ = closeTriangleInequality
              (rational r) (limit x ω) (x δ ξ)
                (ε ℚ.- θ) ((θ ℚ.- δ) ℚ.+ δ) τ α
                υ β

          ζ : (ε ℚ.- θ) ℚ.+ ((θ ℚ.- δ) ℚ.+ δ) ≡ ε
          ζ = (ε ℚ.- θ) ℚ.+ ((θ ℚ.- δ) ℚ.+ δ)
                 ≡⟨ cong (ℚ._+_ (ε ℚ.- θ)) (subtractAddRightCancel δ θ) ⟩
              (ε ℚ.- θ) ℚ.+ θ
                 ≡⟨ subtractAddRightCancel θ ε ⟩
              ε ∎

          γ' : Σ (0 ℚ.< ε) (λ ι → rational r ∼[ ε , ι ] x δ ξ)
          γ' = subst (λ ?x → Σ (0 ℚ.< ?x)
                               (λ ι → rational r ∼[ ?x , ι ] x δ ξ))
                     ζ
                     ((0<+' {x = ε ℚ.- θ} τ α) , γ) 

          γ'' : rational r ∼[ ε , φ ] x δ ξ
          γ'' = subst (λ ?φ → rational r ∼[ ε , ?φ ] x δ ξ)
                      (ℚ.isProp< 0 ε (fst γ') φ)
                      (snd γ')

        z : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ
        z = λ δ ζ → max (rational $ q ℚ.+ ε) (x δ ζ)

        ξ : EventuallyConstantAt θ σ z (rational $ q ℚ.+ ε)
        ξ δ ψ ω = maxCommutative (rational $ q ℚ.+ ε) (x δ ψ) ∙ χ δ ψ (ο δ ψ ω)

        ξ' : EventuallyConstantAt θ σ
               (liftLipschitzApproximation z 1 0<1)
               (rational $ q ℚ.+ ε)
        ξ' δ ψ ω = γ'
          where
          α = ≠-symmetric $ <→≠ 0<1

          β = 0</ {x = δ} {y = 1} ψ 0<1

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
            limit (liftLipschitzApproximation z 1 0<1) _
        α = refl

        β : limit (liftLipschitzApproximation z 1 0<1) _ ≡ rational (q ℚ.+ ε)
        β = eventuallyConstantAt≡constant
              θ σ
              (liftLipschitzApproximation z 1 0<1) _
              (rational $ q ℚ.+ ε)
              ξ'

        γ : max (limit x ω) (rational $ q ℚ.+ ε) ≡ rational (q ℚ.+ ε)
        γ = max (limit x ω) (rational $ q ℚ.+ ε)
              ≡⟨ maxCommutative (limit x ω) (rational $ q ℚ.+ ε) ⟩
            max (rational $ q ℚ.+ ε) (limit x ω)
              ≡⟨ α ⟩
            limit (liftLipschitzApproximation z 1 0<1) _
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
  
