module HoTTReals.Data.Real.Algebra where

import Cubical.Data.Bool as Bool
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Nat.Literals public
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Homotopy.Base
open import Cubical.Algebra.AbGroup.Base

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Lipschitz
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ

instance
  fromNatℝ : HasFromNat ℝ
  fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → rational $ fromNat n }

instance
  fromNegℝ : HasFromNeg ℝ
  fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → rational $ fromNat n }

-- 0ℝ : ℝ
-- 0ℝ = rational {!0!}

-- 1ℝ : ℝ
-- 1ℝ = rational {!!}

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
+lipschitz₁ = nonexpanding₂→lipschitz₁ _+_ +nonexpandingℝ₂

+lipschitz₂ : (u : ℝ) → Lipschitzℝ (_+_ u) 1 0<1
+lipschitz₂ = nonexpanding₂→lipschitz₂ _+_ +nonexpandingℝ₂

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
