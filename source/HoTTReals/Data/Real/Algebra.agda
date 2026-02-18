module HoTTReals.Data.Real.Algebra where

import Cubical.Data.Bool as Bool
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic hiding (⊥; ¬_)
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
open import HoTTReals.Data.Real.Lipschitz
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
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

-lipschitzℚ : Lipschitzℚ (rational ∘ ℚ.-_) 1 ℚ.0<1
-lipschitzℚ q r ε φ ψ =
  rationalRational
    (ℚ.- q) (ℚ.- r)
    (1 ℚ.· ε) (ℚ.0<· {x = 1} {y = ε} ℚ.0<1 φ)
    (ℚ.∣∣<→<₂ {x = (ℚ.- q) ℚ.- (ℚ.- r)} {ε = 1 ℚ.· ε} χ)
    (ℚ.∣∣<→<₁ {x = (ℚ.- q) ℚ.- (ℚ.- r)} {ε = 1 ℚ.· ε} χ)
  where
  ω : ℚ.∣ (ℚ.- q) ℚ.- (ℚ.- r) ∣ ≡ ℚ.∣ q ℚ.- r ∣
  ω = ℚ.-distance q r

  χ : ℚ.∣ (ℚ.- q) ℚ.- (ℚ.- r) ∣ ℚ.< 1 ℚ.· ε
  χ = subst2 ℚ._<_ (sym ω) (sym $ ℚ.·IdL ε) ψ

-_ : ℝ → ℝ
-_ = liftLipschitz (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ

infix  8 -_

-lipschitzℝ : Lipschitzℝ -_ 1 ℚ.0<1
-lipschitzℝ =
  -- The Agda type checker is weird, why do you freeze if I just put this
  -- directly but you finish instantly if I put this in a let block without an
  -- explicit type and then immediately return it?
  let φ = liftLipschitzLipschitz (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ
  in φ

-nonexpandingℝ : Nonexpandingℝ -_
-nonexpandingℝ = lipschitzℝ→nonexpandingℝ -_ -lipschitzℝ

-continuous : Continuous -_
-continuous = lipschitz→continuous -_ 1 ℚ.0<1 -lipschitzℝ

+nonexpandingℚ₂ : Nonexpandingℚ₂ ℚ._+_
+nonexpandingℚ₂ =
  φ , ψ
  where
  φ : (s : ℚ.ℚ) → Nonexpandingℚ (flip ℚ._+_ s)
  φ s q r = ℚ.≡Weaken≤ (ℚ.distance (q ℚ.+ s) (r ℚ.+ s))
                       (ℚ.distance q r)
                       (ℚ.+distanceᵣ q r s)

  ψ : (q : ℚ.ℚ) → Nonexpandingℚ (ℚ._+_ q)
  ψ q r s = ℚ.≡Weaken≤ (ℚ.distance (q ℚ.+ r) (q ℚ.+ s))
                       (ℚ.distance r s)
                       (ℚ.+distanceₗ q r s)

_+_ : ℝ → ℝ → ℝ
_+_ = liftNonexpanding₂ ℚ._+_ +nonexpandingℚ₂

infixl 6 _+_

+nonexpandingℝ₂ : Nonexpandingℝ₂ _+_
+nonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ._+_ +nonexpandingℚ₂

+lipschitz₁ : (v : ℝ) → Lipschitzℝ (flip _+_ v) 1 ℚ.0<1
+lipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ _+_ +nonexpandingℝ₂

+lipschitz₂ : (u : ℝ) → Lipschitzℝ (_+_ u) 1 ℚ.0<1
+lipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ _+_ +nonexpandingℝ₂

+continuous₁ : (v : ℝ) → Continuous (flip _+_ v)
+continuous₁ v = lipschitz→continuous (flip _+_ v) 1 ℚ.0<1 (+lipschitz₁ v)

+continuous₂ : (u : ℝ) → Continuous (_+_ u)
+continuous₂ u = lipschitz→continuous (_+_ u) 1 ℚ.0<1 (+lipschitz₂ u)

-- Need this lame lemma for additive inverse law below.
-- -+lipschitz : Lipschitzℝ (λ u → - u + u) 2 ℚ.0<2
-+lipschitz : Lipschitzℝ (λ u → - u + u) 2 ℚ.0<2
-+lipschitz = lipschitz₂-composeLipschitz₁-lipschitz
  1 1 1 1
  ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
  -lipschitzℝ identityLipschitzℝ +lipschitz₁ +lipschitz₂

_-_ : ℝ → ℝ → ℝ
_-_ x y = x + (- y)

-nonexpandingℝ₂ : Nonexpandingℝ₂ _-_
-nonexpandingℝ₂ = φ , ψ
  where
  φ : (w : ℝ) → Nonexpandingℝ (flip _-_ w)
  φ w u v = fst +nonexpandingℝ₂ (- w) u v

  ψ : (u : ℝ) → Nonexpandingℝ (_-_ u)
  ψ u v w ε φ ψ = 
    nonexpandingCompose
      (_+_ u) -_
      (snd +nonexpandingℝ₂ u) -nonexpandingℝ
      v w
      ε φ
      ψ

infixl 6 _-_

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
              (liftLipschitz≡rational (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ q) ⟩
    rational (ℚ.- q) + rational q
      ≡⟨ liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ (ℚ.- q) q ⟩
    rational (ℚ.- q ℚ.+ q) ∎

  ψ : (q : ℚ.ℚ) → ((λ _ → 0) ∘ rational) q ≡ (rational ∘ (λ _ → 0)) q
  ψ q = refl

  ω : (q : ℚ.ℚ) → (ℚ.- q) ℚ.+ q ≡ 0
  ω = ℚ.+InvL

  χ : Continuous (λ x → - x + x)
  χ = lipschitz→continuous (λ x → - x + x) 2 ℚ.0<2 -+lipschitz

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

ℝAbelianGroup : AbGroup ℓ-zero
ℝAbelianGroup = ℝ , (abgroupstr 0 _+_ -_ isAbelianGroupℝ)

ℝGroup : Group ℓ-zero
ℝGroup = AbGroup→Group ℝAbelianGroup

-involutive : (x : ℝ) → - - x ≡ x
-involutive = GroupTheory.invInv ℝGroup

-- TODO: Remove the next n lemmas in favor of generalized versions

+≡0→≡- : {x y : ℝ} → x + y ≡ 0 → x ≡ - y
+≡0→≡- {x} {y} p =
  x
    ≡⟨ sym (+-unitʳ x) ⟩
  x + 0
    ≡⟨ cong (λ ?x → x + ?x) (sym $ +-inverseᵣ y) ⟩
  x + (y + (- y))
    ≡⟨ (sym $ +-associative x y (- y)) ⟩
  (x + y) + (- y)
    ≡⟨ cong (λ ?x → ?x + (- y)) p ⟩
  0 + (- y)
    ≡⟨ +-unitˡ (- y) ⟩
  - y ∎

negateAdd : (x y : ℝ) → - (x + y) ≡ - x + - y
negateAdd x y = sym $ +≡0→≡- p
  where
  p = (- x + - y) + (x + y)
        ≡⟨ sym $ +-associative (- x + - y) x y ⟩
      ((- x + - y) + x) + y
        ≡⟨ cong (flip _+_ y) (+-associative (- x) (- y) x) ⟩
      (- x + (- y + x)) + y
        ≡⟨ cong (λ ?x → (- x + ?x) + y) (+-commutative (- y) x) ⟩
      (- x + (x + - y)) + y
        ≡⟨ cong (flip _+_ y) (sym $ +-associative (- x) x (- y)) ⟩
      ((- x + x) + - y) + y
        ≡⟨ cong (λ ?x → (?x + - y) + y) (+-inverseₗ x) ⟩
      (0 + - y) + y
        ≡⟨ cong (flip _+_ y) (+-unitˡ $ - y) ⟩
      - y + y
        ≡⟨ +-inverseₗ y ⟩
      0 ∎

addLeftSwap : (x y z : ℝ) → (x + y) + z ≡ (x + z) + y
addLeftSwap x y z = (x + y) + z
                      ≡⟨ +-associative x y z ⟩
                    x + (y + z)
                      ≡⟨ cong (_+_ x) (+-commutative y z) ⟩
                    x + (z + y)
                      ≡⟨ sym (+-associative x z y) ⟩
                    (x + z) + y ∎

addRightSwap : (x y z : ℝ) → x + (y + z) ≡ y + (x + z)
addRightSwap x y z = x + (y + z)
                       ≡⟨ sym (+-associative x y z) ⟩
                     (x + y) + z
                       ≡⟨ cong (flip _+_ z) (+-commutative x y) ⟩
                     (y + x) + z
                       ≡⟨ +-associative y x z ⟩
                     y + (x + z) ∎

addSubtractLeftCancel : (x y : ℝ) → (x + y) - x ≡ y
addSubtractLeftCancel x y = (x + y) - x
                              ≡⟨ addLeftSwap x y (- x) ⟩
                            (x + (- x)) + y
                              ≡⟨ cong (flip _+_ y) (+-inverseᵣ x) ⟩
                            0 + y
                              ≡⟨ +-unitˡ y ⟩
                            y ∎

addSubtractRightCancel : (x y : ℝ) → (x + y) - y ≡ x
addSubtractRightCancel x y = (x + y) - y
                               ≡⟨ +-associative x y (- y) ⟩
                             x + (y - y)
                               ≡⟨ cong (_+_ x) (+-inverseᵣ y) ⟩
                             x + 0
                               ≡⟨ +-unitʳ x ⟩
                             x ∎

subtractAddRightCancel : (x y : ℝ) → (y - x) + x ≡ y
subtractAddRightCancel x y = (y - x) + x
                               ≡⟨ +-associative y (- x) x ⟩
                             y + ((- x) + x)
                               ≡⟨ cong (_+_ y) (+-inverseₗ x) ⟩
                             y + 0
                               ≡⟨ +-unitʳ y ⟩
                             y ∎

negateSubtract : (x y : ℝ) → - (x - y) ≡ - x + y
negateSubtract x y =
  - (x - y)
    ≡⟨ negateAdd x (- y) ⟩
  - x + (- - y)
    ≡⟨ cong (_+_ $ - x) (-involutive y) ⟩
  - x + y ∎

negateSubtract' : (x y : ℝ) → - (x - y) ≡ y - x
negateSubtract' x y = negateSubtract x y ∙ +-commutative (- x) y

maxNonexpandingℚ₂ : Nonexpandingℚ₂ ℚ.max
maxNonexpandingℚ₂ = φ , ψ
  where
  φ : (s : ℚ.ℚ) → Nonexpandingℚ (flip ℚ.max s)
  φ s q r = ℚ.maxNonexpandingˡ q r s

  ψ : (q : ℚ.ℚ) → Nonexpandingℚ (ℚ.max q)
  ψ q r s = ℚ.maxNonexpandingʳ q r s

max : ℝ → ℝ → ℝ
max = liftNonexpanding₂ ℚ.max maxNonexpandingℚ₂

maxNonexpandingℝ₂ : Nonexpandingℝ₂ max
maxNonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ.max maxNonexpandingℚ₂

maxLipschitz₁ : (v : ℝ) → Lipschitzℝ (flip max v) 1 ℚ.0<1
maxLipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ max maxNonexpandingℝ₂

maxLipschitz₂ : (u : ℝ) → Lipschitzℝ (max u) 1 ℚ.0<1
maxLipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ max maxNonexpandingℝ₂

maxContinuous₁ : (v : ℝ) → Continuous (flip max v)
maxContinuous₁ v = lipschitz→continuous (flip max v) 1 ℚ.0<1 (maxLipschitz₁ v)

maxContinuous₂ : (u : ℝ) → Continuous (max u)
maxContinuous₂ u = lipschitz→continuous (max u) 1 ℚ.0<1 (maxLipschitz₂ u)

-- Same deal as x + (- x), see comment above
maxMaxLipschitz : Lipschitzℝ (λ u → max u u) 2 ℚ.0<2
maxMaxLipschitz =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    identityLipschitzℝ identityLipschitzℝ maxLipschitz₁ maxLipschitz₂

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
  π = lipschitz→continuous (λ x → max x x) 2 ℚ.0<2 maxMaxLipschitz
  
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

-- HoTT Lemma 11.3.42
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

-- TODO:
-- <rational→existsBound→<rational :
--   {q : ℚ.ℚ} {x y : ℝ} →
--   x < rational q →
--   ∃ ℚ.ℚ (λ ε → Σ (0 ℚ.< ε) (λ ψ → x ∼[ ε , ψ ] y → y < rational q))
-- <rational→existsBound→<rational {q} {x} {y} φ =
--   ∃-rec isPropPropTrunc ψ φ
--   where
--   ψ : (u : ℚ.ℚ × ℚ.ℚ) →
--       (x ≤ rational (fst u)) ×
--       (fst u ℚ.< snd u) ×
--       (rational (snd u) ≤ rational q) →
--       ∃ ℚ.ℚ (λ ε → Σ (0 ℚ.< ε) (λ ψ → Close ε ψ x y → y < rational q))
--   ψ (r , s) (ω , χ , π) = {!!}

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

minNonexpandingℚ₂ : Nonexpandingℚ₂ ℚ.min
minNonexpandingℚ₂ = φ , ψ
  where
  φ : (s : ℚ.ℚ) → Nonexpandingℚ (flip ℚ.min s)
  φ s q r = ℚ.minNonexpandingˡ q r s

  ψ : (q : ℚ.ℚ) → Nonexpandingℚ (ℚ.min q)
  ψ q r s = ℚ.minNonexpandingʳ q r s

min : ℝ → ℝ → ℝ
min = liftNonexpanding₂ ℚ.min minNonexpandingℚ₂

minNonexpandingℝ₂ : Nonexpandingℝ₂ min
minNonexpandingℝ₂ = liftNonexpanding₂NonExpanding ℚ.min minNonexpandingℚ₂

minLipschitz₁ : (v : ℝ) → Lipschitzℝ (flip min v) 1 ℚ.0<1
minLipschitz₁ = nonexpandingℝ₂→lipschitzℝ₁ min minNonexpandingℝ₂

minLipschitz₂ : (u : ℝ) → Lipschitzℝ (min u) 1 ℚ.0<1
minLipschitz₂ = nonexpandingℝ₂→lipschitzℝ₂ min minNonexpandingℝ₂

minContinuous₁ : (v : ℝ) → Continuous (flip min v)
minContinuous₁ v = lipschitz→continuous (flip min v) 1 ℚ.0<1 (minLipschitz₁ v)

minContinuous₂ : (u : ℝ) → Continuous (min u)
minContinuous₂ u = lipschitz→continuous (min u) 1 ℚ.0<1 (minLipschitz₂ u)

-- Same deal as x + (- x), see comment above
minMinLipschitz : Lipschitzℝ (λ u → min u u) 2 ℚ.0<2
minMinLipschitz =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    identityLipschitzℝ identityLipschitzℝ minLipschitz₁ minLipschitz₂



minAssociative : (x y z : ℝ) → min (min x y) z ≡ min x (min y z)
minAssociative =
  continuousExtensionLaw₃
    associateℝₗ associateℝᵣ associateℚₗ associateℚᵣ
    ψ ω χ π ρ σ τ υ ξ
  where
  associateℝₗ : ℝ → ℝ → ℝ → ℝ
  associateℝₗ x y z = min (min x y) z

  associateℝᵣ : ℝ → ℝ → ℝ → ℝ
  associateℝᵣ x y z = min x (min y z)

  associateℚₗ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚₗ q r s = ℚ.min (ℚ.min q r) s

  associateℚᵣ : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  associateℚᵣ q r s = ℚ.min q (ℚ.min r s)

  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.min minNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.min q r)
  φ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ 

  ψ : (q r s : ℚ.ℚ) →
      associateℝₗ (rational q) (rational r) (rational s) ≡
      rational (associateℚₗ q r s)
  ψ q r s =
    min (min (rational q) (rational r)) (rational s)
      ≡⟨ cong (flip min $ rational s) (φ q r) ⟩
    min (rational (ℚ.min q r)) (rational s)
      ≡⟨ φ (ℚ.min q r) s ⟩
    rational (ℚ.min (ℚ.min q r) s) ∎

  ω : (q r s : ℚ.ℚ) →
      associateℝᵣ (rational q) (rational r) (rational s) ≡
      rational (associateℚᵣ q r s)
  ω q r s =
    min (rational q) (min (rational r) (rational s))
      ≡⟨ cong (min $ rational q) (φ r s) ⟩
    min (rational q) (rational (ℚ.min r s))
      ≡⟨ φ q (ℚ.min r s) ⟩
    rational (ℚ.min q (ℚ.min r s)) ∎

  χ : (q r s : ℚ.ℚ) → associateℚₗ q r s ≡ associateℚᵣ q r s
  χ q r s = sym $ ℚ.minAssoc q r s

  π : (x y : ℝ) → Continuous (associateℝₗ x y)
  π x y = minContinuous₂ (min x y)

  ρ : (x z : ℝ) → Continuous (λ y → associateℝₗ x y z)
  ρ x z = continuousCompose (min x) (flip min z)
                            (minContinuous₂ x) (minContinuous₁ z)

  σ : (y z : ℝ) → Continuous (λ x → associateℝₗ x y z)
  σ y z = continuousCompose (flip min y) (flip min z)
                            (minContinuous₁ y) (minContinuous₁ z)

  τ : (x y : ℝ) → Continuous (associateℝᵣ x y)
  τ x y = continuousCompose (min y) (min x)
                            (minContinuous₂ y) (minContinuous₂ x)

  υ : (x z : ℝ) → Continuous (λ y → associateℝᵣ x y z)
  υ x z = continuousCompose (flip min z) (min x)
                            (minContinuous₁ z) (minContinuous₂ x)

  ξ : (y z : ℝ) → Continuous (λ x → associateℝᵣ x y z)
  ξ y z = minContinuous₁ (min y z)

minCommutative : (x y : ℝ) → min x y ≡ min y x
minCommutative =
  continuousExtensionLaw₂
    min
    (flip min)
    ℚ.min
    (flip ℚ.min)
    φ (flip φ) ψ ω χ χ ω
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.min minNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.min q r)
  φ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ 

  ψ : (x y : ℚ.ℚ) → ℚ.min x y ≡ ℚ.min y x
  ψ = ℚ.minComm

  ω : (u : ℝ) → Continuous (min u)
  ω = minContinuous₂

  χ : (v : ℝ) → Continuous $ flip min v
  χ = minContinuous₁

minIdempotent : (x : ℝ) → min x x ≡ x
minIdempotent =
  continuousExtensionLaw₁
    (λ x → min x x) (idfun ℝ)
    (λ q → ℚ.min q q) (idfun ℚ.ℚ)
    ψ ω χ π ρ
  where
  φ : (q r : ℚ.ℚ) →
      liftNonexpanding₂ ℚ.min minNonexpandingℚ₂ (rational q) (rational r) ≡
      rational (ℚ.min q r)
  φ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ 

  ψ : ((λ x → min x x) ∘ rational) ∼ (rational ∘ (λ q → ℚ.min q q))
  ψ q = φ q q

  ω : (idfun ℝ ∘ rational) ∼ (rational ∘ idfun ℚ.ℚ)
  ω q = refl

  χ : (λ q → ℚ.min q q) ∼ idfun ℚ.ℚ
  χ = ℚ.minIdem

  π : Continuous (λ x → min x x)
  π = lipschitz→continuous (λ x → min x x) 2 ℚ.0<2 minMinLipschitz
  
  ρ : Continuous (idfun ℝ)
  ρ = identityContinuous

min+maxLipschitz₁ : (y : ℝ) → Lipschitzℝ (λ x → min x y + max x y) 2 ℚ.0<2
min+maxLipschitz₁ y =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    (minLipschitz₁ y) (maxLipschitz₁ y) +lipschitz₁ +lipschitz₂

min+maxLipschitz₂ : (x : ℝ) → Lipschitzℝ (λ y → min x y + max x y) 2 ℚ.0<2
min+maxLipschitz₂ x =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    (minLipschitz₂ x) (maxLipschitz₂ x) +lipschitz₁ +lipschitz₂

min+maxContinuous₁ : (y : ℝ) → Continuous (λ x → min x y + max x y)
min+maxContinuous₁ y =
  lipschitz→continuous
    (λ x → min x y + max x y)
    2 ℚ.0<2
    (min+maxLipschitz₁ y)

min+maxContinuous₂ : (x : ℝ) → Continuous (λ y → min x y + max x y)
min+maxContinuous₂ x =
  lipschitz→continuous
    (λ y → min x y + max x y)
    2 ℚ.0<2
    (min+maxLipschitz₂ x)

min+max≡+ : (x y : ℝ) → min x y + max x y ≡ x + y
min+max≡+ =
  continuousExtensionLaw₂
    (λ x y → min x y + max x y)
    _+_
    (λ q r → ℚ.min q r ℚ.+ ℚ.max q r)
    ℚ._+_
    φ ψ ω
    χ π ρ σ
  where
  φ : (q r : ℚ.ℚ) →
      min (rational q) (rational r) + max (rational q) (rational r) ≡
      rational (ℚ.min q r ℚ.+ ℚ.max q r)
  φ q r =
    min (rational q) (rational r) + max (rational q) (rational r)
      ≡⟨ cong (flip _+_ (max (rational q) (rational r)))
              (liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂ q r) ⟩
    rational (ℚ.min q r) + max (rational q) (rational r)
      ≡⟨ cong (_+_ (rational (ℚ.min q r)))
                   (liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ q r) ⟩
    rational (ℚ.min q r) + rational (ℚ.max q r)
      ≡⟨ liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂
                                    (ℚ.min q r) (ℚ.max q r) ⟩
    rational (ℚ.min q r ℚ.+ ℚ.max q r) ∎

  ψ : (q r : ℚ.ℚ) → rational q + rational r ≡ rational (q ℚ.+ r)
  ψ = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

  ω : (q r : ℚ.ℚ) → ℚ.min q r ℚ.+ ℚ.max q r ≡ q ℚ.+ r
  ω = ℚ.min+max≡+

  χ : (u : ℝ) → Continuous $ (λ y → min u y + max u y)
  χ = min+maxContinuous₂

  π : (v : ℝ) → Continuous $ flip (λ x y → min x y + max x y) v
  π = min+maxContinuous₁

  ρ : (u : ℝ) → Continuous $ _+_ u
  ρ = +continuous₂

  σ : (v : ℝ) → Continuous $ flip _+_ v
  σ = +continuous₁

max≡→min≡ : {x y : ℝ} → max x y ≡ y → min x y ≡ x
max≡→min≡ {x} {y} φ = ψ
  where
  φ' : min x y + y ≡ x + y
  φ' = cong (_+_ $ min x y) (sym φ) ∙ min+max≡+ x y

  ψ : min x y ≡ x
  ψ = GroupTheory.·CancelR ℝGroup y φ'

min≡→max≡ : {x y : ℝ} → min x y ≡ x → max x y ≡ y
min≡→max≡ {x} {y} φ = ψ
  where
  φ' : x + max x y ≡ x + y
  φ' = cong (flip _+_ $ max x y) (sym φ) ∙ min+max≡+ x y

  ψ : max x y ≡ y
  ψ = GroupTheory.·CancelL ℝGroup x φ'

∣_∣' : ℝ → ℝ
∣_∣' = liftLipschitz
         (rational ∘ ℚ.∣_∣)
         1 ℚ.0<1
         (nonexpandingℚ→lipschitzℚ ℚ.∣_∣ ℚ.magnitudeNonexpanding)

magnitude'Lipschitzℝ : Lipschitzℝ ∣_∣' 1 ℚ.0<1
magnitude'Lipschitzℝ =
  let φ = liftLipschitzLipschitz
            (rational ∘ ℚ.∣_∣) 1 ℚ.0<1
            (nonexpandingℚ→lipschitzℚ ℚ.∣_∣ ℚ.magnitudeNonexpanding)
  in φ

magnitude'Nonexpandingℝ : Nonexpandingℝ ∣_∣'
magnitude'Nonexpandingℝ = lipschitzℝ→nonexpandingℝ ∣_∣' magnitude'Lipschitzℝ

magnitude'Continuous : Continuous ∣_∣'
magnitude'Continuous = lipschitz→continuous ∣_∣' 1 ℚ.0<1 magnitude'Lipschitzℝ

∣_∣ : ℝ → ℝ
∣ x ∣ = max x (- x)

magnitudeExtendsRationalMagnitude : 
  (∣_∣ ∘ rational) ∼ (rational ∘ ℚ.∣_∣)
magnitudeExtendsRationalMagnitude q =
  max (rational q) (- rational q)
    ≡⟨ cong (max (rational q))
            (liftLipschitz≡rational (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ q) ⟩
  max (rational q) (rational $ ℚ.- q)
    ≡⟨ liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ q (ℚ.- q) ⟩
  rational (ℚ.max q (ℚ.- q)) ∎

magnitudeLipschitzℝ : Lipschitzℝ ∣_∣ 2 ℚ.0<2
magnitudeLipschitzℝ u v ε φ ψ = σ'
  where
  ω : Close ε φ (- u) (- v)
  ω = -nonexpandingℝ u v ε φ ψ

  χ : Close ε φ (max u (- u)) (max u (- v))
  χ = snd maxNonexpandingℝ₂ u (- u) (- v) ε φ ω

  π : Close ε φ (max u (- v)) (max v (- v))
  π = fst maxNonexpandingℝ₂ (- v) u v ε φ ψ

  ρ : Close (ε ℚ.+ ε) (ℚ.0<+' {x = ε} {y = ε} φ φ) (max u (- u)) (max v (- v))
  ρ = closeTriangleInequality
        (max u (- u)) (max u (- v)) (max v (- v))
        ε ε φ φ
        χ π

  σ : Σ (0 ℚ.< 2 ℚ.· ε)
        (λ ξ → Close (2 ℚ.· ε) ξ (max u (- u)) (max v (- v)))
  σ = subst (λ ?x → Σ (0 ℚ.< ?x) (λ ξ → Close ?x ξ _ _))
            (ℚ.self+≡2· ε)
            ((ℚ.0<+' {x = ε} {y = ε} φ φ) , ρ)

  σ' : Close (2 ℚ.· ε) (ℚ.0<· {x = 2} {y = ε} ℚ.0<2 φ) (max u (- u)) (max v (- v))
  σ' = subst (λ ?ξ → Close (2 ℚ.· ε) ?ξ (max u (- u)) (max v (- v)))
             (ℚ.isProp< 0 (2 ℚ.· ε) (fst σ) (ℚ.0<· {x = 2} {y = ε} ℚ.0<2 φ))
             (snd σ)

magnitudeContinuous : Continuous ∣_∣
magnitudeContinuous = lipschitz→continuous ∣_∣ 2 ℚ.0<2 magnitudeLipschitzℝ

magnitude∼magnitude' : ∣_∣ ∼ ∣_∣'
magnitude∼magnitude' =
  continuousExtensionLaw₁ ∣_∣ ∣_∣' ℚ.∣_∣ ℚ.∣_∣
  φ ψ ω
  χ π
  where
  φ : (∣_∣ ∘ rational) ∼ (rational ∘ ℚ.∣_∣)
  φ = magnitudeExtendsRationalMagnitude

  ψ : (∣_∣' ∘ rational) ∼ (rational ∘ ℚ.∣_∣)
  ψ = liftLipschitz≡rational
        (rational ∘ ℚ.∣_∣)
        1 ℚ.0<1
        (nonexpandingℚ→lipschitzℚ ℚ.∣_∣ ℚ.magnitudeNonexpanding)

  ω : ℚ.∣_∣ ∼ ℚ.∣_∣
  ω q = refl

  χ : Continuous ∣_∣
  χ = magnitudeContinuous

  π : Continuous ∣_∣'
  π = magnitude'Continuous

magnitude≡magnitude' : ∣_∣ ≡ ∣_∣'
magnitude≡magnitude' = funExt magnitude∼magnitude'

magnitudeNonexpandingℝ : Nonexpandingℝ ∣_∣
magnitudeNonexpandingℝ =
  subst Nonexpandingℝ (sym magnitude≡magnitude') magnitude'Nonexpandingℝ

maxNegateNegateLipschitz₁ :
  (y : ℝ) → Lipschitzℝ (λ x → max (- x) (- y)) 2 ℚ.0<2
maxNegateNegateLipschitz₁ y =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    -lipschitzℝ (constantLipschitzℝ (- y)) maxLipschitz₁ maxLipschitz₂

maxNegateNegateLipschitz₂ :
  (x : ℝ) → Lipschitzℝ (λ y → max (- x) (- y)) 2 ℚ.0<2
maxNegateNegateLipschitz₂ x =
  lipschitz₂-composeLipschitz₁-lipschitz
    1 1 1 1
    ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
    (constantLipschitzℝ (- x)) -lipschitzℝ maxLipschitz₁ maxLipschitz₂

maxNegateNegateContinuous₁ : (y : ℝ) → Continuous (λ x → max (- x) (- y))
maxNegateNegateContinuous₁ y =
  lipschitz→continuous
    (λ x → max (- x) (- y))
    2 ℚ.0<2
    (maxNegateNegateLipschitz₁ y)

maxNegateNegateContinuous₂ : (x : ℝ) → Continuous (λ y → max (- x) (- y))
maxNegateNegateContinuous₂ x =
  lipschitz→continuous
    (λ y → max (- x) (- y))
    2 ℚ.0<2
    (maxNegateNegateLipschitz₂ x)

negateMaxNegateNegate≡min : (x y : ℝ) → - max (- x) (- y) ≡ min x y
negateMaxNegateNegate≡min =
  continuousExtensionLaw₂
    (λ x y → - max (- x) (- y)) min
    (λ q r → ℚ.- ℚ.max (ℚ.- q) (ℚ.- r)) ℚ.min
    φ ψ ω χ π ρ σ
  where
  φ : (q r : ℚ.ℚ) →
      - max (- rational q) (- rational r) ≡
      rational (ℚ.- ℚ.max (ℚ.- q) (ℚ.- r))
  φ q r = - max (- rational q) (- rational r)
            ≡⟨ cong (λ ?x → - max ?x (- rational r))
                    (liftLipschitz≡rational
                      (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ q) ⟩
          - max (rational (ℚ.- q)) (- rational r)
            ≡⟨ cong (λ ?x → - max (rational (ℚ.- q)) ?x)
                    (liftLipschitz≡rational
                      (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ r) ⟩
          - max (rational (ℚ.- q)) (rational (ℚ.- r))
            ≡⟨ cong -_ (liftNonexpanding₂≡rational
                         ℚ.max maxNonexpandingℚ₂ (ℚ.- q) (ℚ.- r)) ⟩
          - rational (ℚ.max (ℚ.- q) (ℚ.- r))
            ≡⟨ liftLipschitz≡rational
                 (rational ∘ ℚ.-_) 1 ℚ.0<1 -lipschitzℚ (ℚ.max (ℚ.- q) (ℚ.- r)) ⟩
          rational (ℚ.- (ℚ.max (ℚ.- q) (ℚ.- r))) ∎

  ψ : (q r : ℚ.ℚ) → min (rational q) (rational r) ≡ rational (ℚ.min q r)
  ψ = liftNonexpanding₂≡rational ℚ.min minNonexpandingℚ₂

  ω : (q r : ℚ.ℚ) → (ℚ.- ℚ.max (ℚ.- q) (ℚ.- r)) ≡ ℚ.min q r
  ω = ℚ.negateMaxNegateNegate≡min

  χ : (u : ℝ) → Continuous $ (λ y → - max (- u) (- y))
  χ u = continuousCompose
          (λ y → max (- u) (- y)) -_
          (maxNegateNegateContinuous₂ u) -continuous

  π : (v : ℝ) → Continuous $ flip (λ x y → - max (- x) (- y)) v
  π v = continuousCompose
          (λ x → max (- x) (- v)) -_
          (maxNegateNegateContinuous₁ v) -continuous

  ρ : (u : ℝ) → Continuous $ min u
  ρ = minContinuous₂

  σ : (v : ℝ) → Continuous $ flip min v
  σ = minContinuous₁

negateMinNegateNegate≡max : (x y : ℝ) → - min (- x) (- y) ≡ max x y
negateMinNegateNegate≡max x y = ψ
  where
  φ : - max (- - x) (- - y) ≡ min (- x) (- y)
  φ = negateMaxNegateNegate≡min (- x) (- y)

  φ' : max (- - x) (- - y) ≡ - min (- x) (- y)
  φ' = sym (-involutive _) ∙ cong -_ φ

  ψ : - min (- x) (- y) ≡ max x y
  ψ = sym φ' ∙ cong₂ max (-involutive x) (-involutive y)

-antitone≤ : {x y : ℝ} → x ≤ y → - y ≤ - x
-antitone≤ {x} {y} φ = π
  where
  ψ : min x y ≡ x
  ψ = max≡→min≡ φ

  ω : - max (- x) (- y) ≡ x
  ω = negateMaxNegateNegate≡min x y ∙ ψ

  χ : max (- x) (- y) ≡ - x
  χ = sym (-involutive _) ∙ cong -_ ω

  π : max (- y) (- x) ≡ - x
  π = maxCommutative (- y) (- x) ∙ χ

-antitone< : {x y : ℝ} → x < y → - y < - x
-antitone< {x} {y} = ∃-rec (<-isProp (- y) (- x)) φ
  where
  φ : (u : ℚ.ℚ × ℚ.ℚ) →
      (x ≤ rational (fst u)) × ((fst u) ℚ.< (snd u)) × (rational (snd u) ≤ y) →
      - y < - x
  φ (q , r) (ψ , ω , χ) = ∣ (ℚ.- r , ℚ.- q) , (χ' , ω' , ψ') ∣₁
    where
    χ' : - y ≤ rational (ℚ.- r)
    χ' = -antitone≤ {x = rational r} {y = y} χ

    ω' : ℚ.- r ℚ.< ℚ.- q
    ω' = ℚ.<antitone- {x = q} {y = r} ω

    ψ' : rational (ℚ.- q) ≤ - x
    ψ' = -antitone≤ {x = x} {y = rational q} ψ

magnitudeNegate≡magnitude : (x : ℝ) → ∣ - x ∣ ≡ ∣ x ∣
magnitudeNegate≡magnitude x =
  max (- x) (- - x)
    ≡⟨ cong (max (- x)) (-involutive x) ⟩
  max (- x) x
    ≡⟨ maxCommutative (- x) x ⟩
  max x (- x) ∎

self≤∣∣ : (x : ℝ) → x ≤ ∣ x ∣
self≤∣∣ x = ≤-max₁ x (- x)

-∣∣≤self : (x : ℝ) → - ∣ x ∣ ≤ x
-∣∣≤self x = ω
  where
  φ : - x ≤ ∣ - x ∣
  φ = self≤∣∣ (- x)

  ψ : - ∣ - x ∣ ≤ - - x
  ψ = -antitone≤ {x = - x} {y = ∣ - x ∣} φ 

  ω : - ∣ x ∣ ≤ x
  ω = subst2 _≤_ (cong -_ (magnitudeNegate≡magnitude x)) (-involutive x) ψ

≡0→magnitude≡0 : {x : ℝ} → x ≡ 0 → ∣ x ∣ ≡ 0
≡0→magnitude≡0 {x} φ = ω
  where
  ψ : ∣ 0 ∣ ≡ 0
  ψ = refl

  ω : ∣ x ∣ ≡ 0
  ω = cong ∣_∣ φ ∙ ψ

magnitudeMagnitude≡magnitude : (x : ℝ) → ∣ ∣ x ∣ ∣ ≡ ∣ x ∣
magnitudeMagnitude≡magnitude x = χ
  where
  φ : - ∣ x ∣ ≤ x
  φ = -∣∣≤self x

  ψ : x ≤ ∣ x ∣
  ψ = self≤∣∣ x

  ω : - ∣ x ∣ ≤ ∣ x ∣
  ω = ≤-transitive (- ∣ x ∣) x ∣ x ∣ φ ψ

  χ : max ∣ x ∣ (- ∣ x ∣) ≡ ∣ x ∣
  χ = maxCommutative ∣ x ∣ (- ∣ x ∣) ∙ ω

-- TODO:
-- magnitude≡0→≡0 : {x : ℝ} → ∣ x ∣ ≡ 0 → x ≡ 0
-- magnitude≡0→≡0 {x} φ = {!!}

0≤magnitude : (x : ℝ) → 0 ≤ ∣ x ∣
0≤magnitude =
  continuousExtensionLaw₁
    f g f' g'
    H K L φ ψ
  where
  f : ℝ → ℝ
  f x = max 0 (max x (- x))

  g : ℝ → ℝ
  g = ∣_∣

  f' : ℚ.ℚ → ℚ.ℚ
  f' q = ℚ.max 0 (ℚ.∣ q ∣)

  g' : ℚ.ℚ → ℚ.ℚ
  g' = ℚ.∣_∣

  H : (f ∘ rational) ∼ (rational ∘ f')
  H q = max 0 ∣ rational q ∣
          ≡⟨ cong (max 0) (magnitudeExtendsRationalMagnitude q) ⟩
        max 0 (rational (ℚ.∣ q ∣))
          ≡⟨ liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂ 0 (ℚ.∣ q ∣) ⟩
        rational (ℚ.max 0 (ℚ.∣ q ∣)) ∎

  K : (g ∘ rational) ∼ (rational ∘ g')
  K = magnitudeExtendsRationalMagnitude

  L : f' ∼ g'
  L q = ℚ.≤→max 0 ℚ.∣ q ∣ (ℚ.0≤∣∣ q)

  φ : Continuous f
  φ = continuousCompose ∣_∣ (max 0) magnitudeContinuous (maxContinuous₂ 0)

  ψ : Continuous g
  ψ = magnitudeContinuous

distance : ℝ → ℝ → ℝ
distance x y = ∣ x - y ∣

distanceNonexpandingℝ₂ : Nonexpandingℝ₂ distance
distanceNonexpandingℝ₂ = φ , ψ
  where
  φ : (w : ℝ) → Nonexpandingℝ (flip distance w)
  φ w = nonexpandingCompose
          ∣_∣ (flip _-_ w)
          magnitudeNonexpandingℝ (fst -nonexpandingℝ₂ w)

  ψ : (u : ℝ) → Nonexpandingℝ (distance u)
  ψ u = nonexpandingCompose
          ∣_∣ (_-_ u)
          magnitudeNonexpandingℝ (snd -nonexpandingℝ₂ u)

distanceExtendsRationalDistance : (q r : ℚ.ℚ) →
  distance (rational q) (rational r) ≡ rational (ℚ.distance q r)
distanceExtendsRationalDistance q r =
  cong ∣_∣ (liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂ q (ℚ.- r))

0≤distance : (x y : ℝ) → 0 ≤ distance x y
0≤distance x y = 0≤magnitude (x - y)

close-0→magnitude< :
  {x : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x ∼[ ε , φ ] 0 →
  ∣ x ∣ < rational ε
close-0→magnitude< {x} {ε} =
  inductionProposition {A = P} (φ , ψ , χ) x ε
  where
  P : ℝ → Type ℓ-zero
  P x = (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) → x ∼[ ε , φ ] 0 → ∣ x ∣ < rational ε

  φ : (q : ℚ.ℚ) (ε : ℚ.ℚ) (ψ : 0 ℚ.< ε) →
      rational q ∼[ ε , ψ ] 0 →
      ∣ rational q ∣ < rational ε
  φ q ε ψ ω = τ
    where
    π : ℚ.∣ q ℚ.- 0 ∣ ℚ.< ε
    π = close→close' (rational q) 0 ε ψ ω

    ρ : ℚ.∣ q ∣ ℚ.< ε
    ρ = subst (ℚ._< ε) (cong ℚ.∣_∣ $ ℚ.+IdR q) π

    τ : rational ℚ.∣ q ∣ < rational ε
    τ = rationalStrictMonotone {ℚ.∣ q ∣} {ε} ρ

    τ' : ∣ rational q ∣ < rational ε
    τ' = subst (_< rational ε)
               (sym $ magnitudeExtendsRationalMagnitude q)
               τ

  ψ : (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (ω : CauchyApproximation x) →
      ((δ : ℚ.ℚ) (χ : 0 ℚ.< δ) →
       (ε : ℚ.ℚ) (π : 0 ℚ.< ε) →
       x δ χ ∼[ ε , π ] 0 →
       ∣ x δ χ ∣ < rational ε) →
      (ε : ℚ.ℚ) (π : 0 ℚ.< ε) →
      limit x ω ∼[ ε , π ] 0 →
      ∣ limit x ω ∣ < rational ε
  ψ x ω χ ε π ρ =
    ∃-rec (<-isProp ∣ limit x ω ∣ (rational ε))
          ψ'
          (closeOpen (limit x ω) 0 ε π ρ)
    where
    ψ' : (θ : ℚ.ℚ) →
         (0 ℚ.< θ) × Σ (0 ℚ.< ε ℚ.- θ) (λ σ → limit x ω ∼[ ε ℚ.- θ , σ ] 0) →
         ∣ limit x ω ∣ < rational ε
    ψ' θ (σ , τ , υ) = κ'
      where
      α : 0 ℚ.< θ / 4 [ ℚ.4≠0 ]
      α = ℚ.0</ {x = θ} {y = 4} σ ℚ.0<4

      α' : 0 ℚ.< θ / 2 [ ℚ.2≠0 ]
      α' = ℚ.0</ {x = θ} {y = 2} σ ℚ.0<2

      β : Close ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
                (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α)
                (x (θ / 4 [ ℚ.4≠0 ]) α)
                (limit x ω)
      β = closeLimit'' x ω (θ / 4 [ ℚ.4≠0 ]) (θ / 4 [ ℚ.4≠0 ]) α α

      γ : x (θ / 4 [ ℚ.4≠0 ]) α
          ∼[ ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ) ,
             ℚ.0<+'
               {x = ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))} {y = ε ℚ.- θ}
               (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} α α) τ ]
          0
      γ = closeTriangleInequality
            (x (θ / 4 [ ℚ.4≠0 ]) α) (limit x ω) 0
            ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) (ε ℚ.- θ)
            (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} α α) τ
            β υ

      ζ : ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ) ≡
          ε ℚ.- (θ / 2 [ ℚ.2≠0 ])
      ζ = ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ)
            ≡⟨ cong (flip ℚ._+_ $ ε ℚ.- θ) (ℚ.self/4≡self/2 θ ℚ.4≠0 ℚ.2≠0) ⟩
          (θ / 2 [ ℚ.2≠0 ]) ℚ.+ (ε ℚ.- θ)
            ≡⟨ ℚ.addRightSwap (θ / 2 [ ℚ.2≠0 ]) ε (ℚ.- θ) ⟩
          ε ℚ.+ ((θ / 2 [ ℚ.2≠0 ]) ℚ.- θ)
            ≡⟨ cong (ℚ._+_ ε) (sym $ ℚ.negateSubtract' θ (θ / 2 [ ℚ.2≠0 ])) ⟩
          ε ℚ.- (θ ℚ.- (θ / 2 [ ℚ.2≠0 ]))
            ≡⟨ cong (ℚ._-_ ε) (ℚ.self-self/2≡self/2 θ) ⟩
          ε ℚ.- (θ / 2 [ ℚ.2≠0 ]) ∎

      ι : ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣ <
          rational (((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ))
      ι = χ (θ / 4 [ ℚ.4≠0 ]) α
            (((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ℚ.+ (ε ℚ.- θ))
            (ℚ.0<+'
               {x = ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))} {y = ε ℚ.- θ}
               (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} α α) τ)
            γ 

      ι' : ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣ <
           rational (ε ℚ.- (θ / 2 [ ℚ.2≠0 ]))
      ι' = subst (_<_ ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣) (cong rational ζ) ι

      β' : Close ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
                 (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α)
                 ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣
                 ∣ limit x ω ∣
      β' = magnitudeNonexpandingℝ
             (x (θ / 4 [ ℚ.4≠0 ]) α) (limit x ω)
             ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
             (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α)
             β

      κ : ∣ limit x ω ∣ <
          rational ((ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+
                    ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])))
      κ = <rational→close→<rational+ε
            {x = ∣ x (θ / 4 [ ℚ.4≠0 ]) α ∣} {y = ∣ limit x ω ∣}
            (ℚ.0<+' {x = θ / 4 [ ℚ.4≠0 ]} {y = θ / 4 [ ℚ.4≠0 ]} α α) ι' β'

      μ : (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+
          ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ])) ≡
          ε
      μ = (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+
          ((θ / 4 [ ℚ.4≠0 ]) ℚ.+ (θ / 4 [ ℚ.4≠0 ]))
            ≡⟨ cong (ℚ._+_ (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])))
                    (ℚ.self/4≡self/2 θ ℚ.4≠0 ℚ.2≠0) ⟩ 
          (ε ℚ.- (θ / 2 [ ℚ.2≠0 ])) ℚ.+ (θ / 2 [ ℚ.2≠0 ])
            ≡⟨ (sym $ ℚ.+Assoc ε (ℚ.- (θ / 2 [ ℚ.2≠0 ])) (θ / 2 [ ℚ.2≠0 ])) ⟩ 
          ε ℚ.+ (ℚ.- (θ / 2 [ ℚ.2≠0 ]) ℚ.+ (θ / 2 [ ℚ.2≠0 ]))
            ≡⟨ cong (ℚ._+_ ε) (ℚ.+InvL (θ / 2 [ ℚ.2≠0 ])) ⟩ 
          ε ℚ.+ 0
            ≡⟨ ℚ.+IdR ε ⟩ 
          ε ∎

      κ' : ∣ limit x ω ∣ < rational ε
      κ' = subst (∣ limit x ω ∣ <_) (cong rational μ) κ

  χ : (x : ℝ) → isProp (P x)
  χ x = isPropΠ3 (λ ε φ ψ → <-isProp ∣ x ∣ (rational ε))

close→distance< :
  {x y : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  x ∼[ ε , φ ] y →
  distance x y < rational ε
close→distance< {x} {y} {ε} φ ψ = χ'
  where
  ω : ∣ x - y ∣ ∼[ ε , φ ] ∣ y - y ∣
  ω = fst distanceNonexpandingℝ₂ y x y ε φ ψ

  ω' : ∣ x - y ∣ ∼[ ε , φ ] 0
  ω' = subst (λ ?x → ∣ x - y ∣ ∼[ ε , φ ] ?x) (≡0→magnitude≡0 $ +-inverseᵣ y) ω
  
  χ : ∣ ∣ x - y ∣ ∣ < rational ε
  χ = close-0→magnitude< φ ω'

  χ' : ∣ x - y ∣ < rational ε
  χ' = subst (flip _<_ $ rational ε) (magnitudeMagnitude≡magnitude $ x - y) χ

distance<→close : 
  {x y : ℝ} {ε : ℚ.ℚ} (φ : 0 ℚ.< ε) →
  distance x y < rational ε →
  x ∼[ ε , φ ] y
distance<→close {x} {y} {ε} =
  inductionProposition₂ {A = P}
  (rationalRationalCase ,
   rationalLimitCase ,
   limitRationalCase ,
   limitLimitCase ,
   pProposition)
  x y ε
  where
  P : ℝ → ℝ → Type ℓ-zero
  P x y = (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) → distance x y < rational ε → x ∼[ ε , φ ] y

  rationalRationalCase :
    (q r : ℚ.ℚ) →
    (ε : ℚ.ℚ) (φ : 0 ℚ.< ε) →
    distance (rational q) (rational r) < rational ε →
    (rational q) ∼[ ε , φ ] (rational r)
  rationalRationalCase q r ε φ ψ = χ
    where
    ω : distance (rational q) (rational r) ≡ rational (ℚ.distance q r)
    ω = distanceExtendsRationalDistance q r

    ψ' : rational (ℚ.distance q r) < rational ε
    ψ' = subst (flip _<_ $ rational ε) ω ψ

    ψ'' : ℚ.distance q r ℚ.< ε
    ψ'' = rationalStrictReflective {q = ℚ.distance q r} {r = ε} ψ'

    χ : rational q ∼[ ε , φ ] rational r
    χ = close'→close (rational q) (rational r) ε φ ψ''

  rationalLimitCase :
    (q : ℚ.ℚ) (y : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (φ : CauchyApproximation y) →
    ((δ : ℚ.ℚ) (ψ : 0 ℚ.< δ) →
     (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
     distance (rational q) (y δ ψ) < rational ε →
     (rational q) ∼[ ε , ω ] (y δ ψ)) →
    (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
    distance (rational q) (limit y φ) < rational ε →
    (rational q) ∼[ ε , ω ] (limit y φ)
  rationalLimitCase q y φ ψ ε ω χ =
    ∃-rec (squash ε ω (rational q) (limit y φ)) rationalLimitCase'
          (<-archimedian (distance (rational q) (limit y φ)) (rational ε) χ)
    where
    rationalLimitCase' :
      (θ : ℚ.ℚ) →
      (distance (rational q) (limit y φ) < rational θ) ×
      (rational θ < rational ε) →
      rational q ∼[ ε , ω ] limit y φ
    rationalLimitCase' θ (π , ρ) = ζ''
      where
      σ : 0 ℚ.< θ
      σ = rationalStrictReflective {q = 0} {r = θ}
            (≤→<→< {x = 0} (0≤distance (rational q) (limit y φ)) π)

      ρ' : θ ℚ.< ε
      ρ' = rationalStrictReflective {q = θ} {r = ε} ρ

      τ : 0 ℚ.< ε ℚ.- θ
      τ = ℚ.<→0<- {x = θ} {y = ε} ρ'

      δ : ℚ.ℚ
      δ = (ε ℚ.- θ) / 4 [ ℚ.4≠0 ]

      σ' : 0 ℚ.< δ
      σ' = ℚ.0</ {x = ε ℚ.- θ} {y = 4} τ ℚ.0<4

      υ : limit y φ ∼[ (δ ℚ.+ δ) , ℚ.0<+' {x = δ} {y = δ} σ' σ' ] y δ σ'
      υ = limitClose'' y φ δ δ σ' σ'

      υ' : y δ σ' ∼[ (δ ℚ.+ δ) , ℚ.0<+' {x = δ} {y = δ} σ' σ' ] limit y φ
      υ' = closeSymmetric (limit y φ) (y δ σ') (δ ℚ.+ δ)
                          (ℚ.0<+' {x = δ} {y = δ} σ' σ') υ

      α : distance (rational q) (limit y φ)
          ∼[ δ ℚ.+ δ , ℚ.0<+' {x = δ} {y = δ} σ' σ' ]
          distance (rational q) (y δ σ')
      α = snd distanceNonexpandingℝ₂
            (rational q) (limit y φ) (y δ σ')
            (δ ℚ.+ δ) (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            υ

      β : distance (rational q) (y δ σ') < rational (θ ℚ.+ (δ ℚ.+ δ))
      β = <rational→close→<rational+ε (ℚ.0<+' {x = δ} {y = δ} σ' σ') π α

      γ : rational q
          ∼[ θ ℚ.+ (δ ℚ.+ δ) ,
             ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ') ]
          y δ σ'
      γ = ψ δ
            σ'
            (θ ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            β

      ζ : rational q ∼[ (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ) , _ ] limit y φ
      ζ = closeTriangleInequality
            (rational q) (y δ σ') (limit y φ)
            (θ ℚ.+ (δ ℚ.+ δ)) (δ ℚ.+ δ)
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ
              (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            γ υ'

      ι' : (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ) ≡ ε ℚ.- θ
      ι' = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)
            ≡⟨ cong₂ ℚ._+_
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0)
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0) ⟩
          ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ]) ℚ.+ ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ])
            ≡⟨ ℚ.self/2≡self (ε ℚ.- θ) ℚ.2≠0 ⟩
          ε ℚ.- θ ∎

      ι : (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ) ≡ ε
      ι = (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)
            ≡⟨ sym $ ℚ.+Assoc θ (δ ℚ.+ δ) (δ ℚ.+ δ) ⟩
          θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))
            ≡⟨ cong (ℚ._+_ θ) ι' ⟩
          θ ℚ.+ (ε ℚ.- θ)
            ≡⟨ ℚ.addLeftSubtractCancel θ ε ⟩
          ε ∎

      ζ' : Σ (0 ℚ.< ε)
             (λ ?ξ → Close ε ?ξ (rational q) (limit y φ))
      ζ' = subst (λ ?x → Σ (0 ℚ.< ?x)
                           (λ ξ → Close ?x ξ (rational q) (limit y φ)))
                 ι
                 (_ , ζ)

      ζ'' : rational q ∼[ ε , ω ] limit y φ
      ζ'' = subst (λ ?ξ → Close ε ?ξ (rational q) (limit y φ))
                  (ℚ.isProp< 0 ε (fst ζ') ω)
                  (snd ζ') 

  limitRationalCase :
    (x : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ) (φ : CauchyApproximation x) (r : ℚ.ℚ) →
    ((δ : ℚ.ℚ) (ψ : 0 ℚ.< δ) →
     (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
     distance (x δ ψ) (rational r) < rational ε →
     x δ ψ ∼[ ε , ω ] rational r) →
    (ε : ℚ.ℚ) (ω : 0 ℚ.< ε) →
    distance (limit x φ) (rational r) < rational ε →
    limit x φ ∼[ ε , ω ] rational r
  limitRationalCase x φ r ψ ε ω χ =
    ∃-rec (squash ε ω (limit x φ) (rational r)) limitRationalCase'
          (<-archimedian (distance (limit x φ) (rational r)) (rational ε) χ)
    where
    limitRationalCase' :
      (θ : ℚ.ℚ) →
      (distance (limit x φ) (rational r) < rational θ) ×
      (rational θ < rational ε) →
      limit x φ ∼[ ε , ω ] rational r
    limitRationalCase' θ (π , ρ) = ζ''
      where
      σ : 0 ℚ.< θ
      σ = rationalStrictReflective {q = 0} {r = θ}
            (≤→<→< {x = 0} (0≤distance (limit x φ) (rational r)) π)

      ρ' : θ ℚ.< ε
      ρ' = rationalStrictReflective {q = θ} {r = ε} ρ

      τ : 0 ℚ.< ε ℚ.- θ
      τ = ℚ.<→0<- {x = θ} {y = ε} ρ'

      δ : ℚ.ℚ
      δ = (ε ℚ.- θ) / 4 [ ℚ.4≠0 ]

      σ' : 0 ℚ.< δ
      σ' = ℚ.0</ {x = ε ℚ.- θ} {y = 4} τ ℚ.0<4

      υ : limit x φ ∼[ (δ ℚ.+ δ) , ℚ.0<+' {x = δ} {y = δ} σ' σ' ] x δ σ'
      υ = limitClose'' x φ δ δ σ' σ'

      α : distance (limit x φ) (rational r)
          ∼[ δ ℚ.+ δ , ℚ.0<+' {x = δ} {y = δ} σ' σ' ]
          distance (x δ σ') (rational r)
      α = fst distanceNonexpandingℝ₂
            (rational r) (limit x φ) (x δ σ')
            (δ ℚ.+ δ) (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            υ

      β : distance (x δ σ') (rational r) < rational (θ ℚ.+ (δ ℚ.+ δ))
      β = <rational→close→<rational+ε (ℚ.0<+' {x = δ} {y = δ} σ' σ') π α

      γ : x δ σ'
          ∼[ θ ℚ.+ (δ ℚ.+ δ) ,
             ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ') ]
          rational r
      γ = ψ δ
            σ'
            (θ ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            β

      ζ : limit x φ ∼[ (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ (δ ℚ.+ δ)) , _ ] rational r
      ζ = closeTriangleInequality
            (limit x φ) (x δ σ') (rational r)
            (δ ℚ.+ δ) (θ ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = δ} {y = δ} σ' σ')
            (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ
              (ℚ.0<+' {x = δ} {y = δ} σ' σ'))
            υ γ

      ι' : (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ) ≡ ε ℚ.- θ
      ι' = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)
            ≡⟨ cong₂ ℚ._+_
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0)
                     (ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0) ⟩
          ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ]) ℚ.+ ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ])
            ≡⟨ ℚ.self/2≡self (ε ℚ.- θ) ℚ.2≠0 ⟩
          ε ℚ.- θ ∎

      ι : (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ (δ ℚ.+ δ)) ≡ ε
      ι = (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ (δ ℚ.+ δ))
            ≡⟨ ℚ.addRightSwap (δ ℚ.+ δ) θ (δ ℚ.+ δ) ⟩
          θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))
            ≡⟨ cong (ℚ._+_ θ) ι' ⟩
          θ ℚ.+ (ε ℚ.- θ)
            ≡⟨ ℚ.addLeftSubtractCancel θ ε ⟩
          ε ∎

      ζ' : Σ (0 ℚ.< ε)
             (λ ?ξ → Close ε ?ξ (limit x φ) (rational r))
      ζ' = subst (λ ?x → Σ (0 ℚ.< ?x)
                           (λ ξ → Close ?x ξ (limit x φ) (rational r)))
                 ι
                 (_ , ζ)

      ζ'' : limit x φ ∼[ ε , ω ] rational r
      ζ'' = subst (λ ?ξ → Close ε ?ξ (limit x φ) (rational r))
                  (ℚ.isProp< 0 ε (fst ζ') ω)
                  (snd ζ')

  limitLimitCase :
    (x y : (ε : ℚ.ℚ) → 0 ℚ.< ε → ℝ)
    (φ : CauchyApproximation x)
    (ψ : CauchyApproximation y) →
    ((δ η : ℚ.ℚ) (ω : 0 ℚ.< δ) (χ : 0 ℚ.< η)
     (ε : ℚ.ℚ) (π : 0 ℚ.< ε) →
     distance (x δ ω) (y η χ) < rational ε →
     x δ ω ∼[ ε , π ] y η χ) →
    (ε : ℚ.ℚ) (χ : 0 ℚ.< ε) →
    distance (limit x φ) (limit y ψ) < rational ε →
    limit x φ ∼[ ε , χ ] limit y ψ
  limitLimitCase x y φ ψ ω ε χ π =
    ∃-rec (squash ε χ (limit x φ) (limit y ψ)) limitLimitCase'
          (<-archimedian (distance (limit x φ) (limit y ψ)) (rational ε) π)
    where
    limitLimitCase' :
      (θ : ℚ.ℚ) →
      (distance (limit x φ) (limit y ψ) < rational θ) ×
      (rational θ < rational ε) →
      limit x φ ∼[ ε , χ ] limit y ψ
    limitLimitCase' θ (π' , ρ) = ζ₄
      where
      σ : 0 ℚ.< θ
      σ = rationalStrictReflective {q = 0} {r = θ}
            (≤→<→< {x = 0} (0≤distance (limit x φ) (limit y ψ)) π')

      ρ' : θ ℚ.< ε
      ρ' = rationalStrictReflective {q = θ} {r = ε} ρ

      ρ'' : 0 ℚ.< ε ℚ.- θ
      ρ'' = ℚ.<→0<- {x = θ} {y = ε} ρ'

      δ : ℚ.ℚ
      δ = (ε ℚ.- θ) / 8 [ ℚ.8≠0 ]

      τ : 0 ℚ.< δ
      τ = ℚ.0</ {x = ε ℚ.- θ} {y = 8} ρ'' ℚ.0<8

      τ' : 0 ℚ.< δ ℚ.+ δ
      τ' = ℚ.0<+' {x = δ} {y = δ} τ τ

      υₓ : limit x φ ∼[ δ ℚ.+ δ , τ' ] x δ τ
      υₓ = limitClose'' x φ δ δ τ τ

      υᵧ : limit y ψ ∼[ δ ℚ.+ δ , τ' ] y δ τ
      υᵧ = limitClose'' y ψ δ δ τ τ

      υᵧ' : y δ τ ∼[ δ ℚ.+ δ , τ' ] limit y ψ
      υᵧ' = closeSymmetric (limit y ψ) (y δ τ) (δ ℚ.+ δ) τ' υᵧ

      α₁ : distance (limit x φ) (limit y ψ)
           ∼[ δ ℚ.+ δ , τ' ]
           distance (x δ τ) (limit y ψ)
      α₁ = fst distanceNonexpandingℝ₂
             (limit y ψ) (limit x φ) (x δ τ)
             (δ ℚ.+ δ) τ' υₓ

      β₁ : distance (x δ τ) (limit y ψ) < rational (θ ℚ.+ (δ ℚ.+ δ))
      β₁ = <rational→close→<rational+ε τ' π' α₁

      α₂ : distance (x δ τ) (limit y ψ)
           ∼[ δ ℚ.+ δ , τ' ]
           distance (x δ τ) (y δ τ)
      α₂ = snd distanceNonexpandingℝ₂
             (x δ τ) (limit y ψ) (y δ τ)
             (δ ℚ.+ δ) τ' υᵧ

      β₂ : distance (x δ τ) (y δ τ) < rational ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
      β₂ = <rational→close→<rational+ε τ' β₁ α₂

      γ : x δ τ
          ∼[ (θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ) ,
             ℚ.0<+' {x = θ ℚ.+ (δ ℚ.+ δ)} {y = δ ℚ.+ δ}
               (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ τ') τ' ]
          y δ τ
      γ = ω δ δ τ τ
            ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
            (ℚ.0<+' {x = θ ℚ.+ (δ ℚ.+ δ)} {y = δ ℚ.+ δ}
               (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ τ') τ')
            β₂

      ζ₁ : limit x φ
           ∼[ (δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)) , _ ]
           y δ τ
      ζ₁ = closeTriangleInequality
             (limit x φ) (x δ τ) (y δ τ)
             (δ ℚ.+ δ) ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
             τ'
             (ℚ.0<+' {x = θ ℚ.+ (δ ℚ.+ δ)} {y = δ ℚ.+ δ}
               (ℚ.0<+' {x = θ} {y = δ ℚ.+ δ} σ τ') τ')
             υₓ γ

      ζ₂ : limit x φ
           ∼[ ((δ ℚ.+ δ) ℚ.+
              ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) ℚ.+ (δ ℚ.+ δ) , _ ]
           limit y ψ
      ζ₂ = closeTriangleInequality
            (limit x φ) (y δ τ) (limit y ψ)
            ((δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) (δ ℚ.+ δ)
            _ τ'
            ζ₁ υᵧ'

      η₁ : δ ℚ.+ δ ≡ (ε ℚ.- θ) / 4 [ ℚ.4≠0 ]
      η₁ = ℚ.self/8≡self/4 (ε ℚ.- θ) ℚ.8≠0 ℚ.4≠0

      η₂ : (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ) ≡ (ε ℚ.- θ) / 2 [ ℚ.2≠0 ]
      η₂ = (δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)
             ≡⟨ cong₂ ℚ._+_ η₁ η₁ ⟩
           ((ε ℚ.- θ) / 4 [ ℚ.4≠0 ]) ℚ.+ ((ε ℚ.- θ) / 4 [ ℚ.4≠0 ])
             ≡⟨ ℚ.self/4≡self/2 (ε ℚ.- θ) ℚ.4≠0 ℚ.2≠0 ⟩
           (ε ℚ.- θ) / 2 [ ℚ.2≠0 ] ∎

      η₃ : ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ≡ ε ℚ.- θ
      η₃ = ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))
             ≡⟨ cong₂ ℚ._+_ η₂ η₂ ⟩
           ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ]) ℚ.+ ((ε ℚ.- θ) / 2 [ ℚ.2≠0 ])
             ≡⟨ ℚ.self/2≡self (ε ℚ.- θ) ℚ.2≠0 ⟩
           ε ℚ.- θ ∎

      ι : ((δ ℚ.+ δ) ℚ.+
          ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) ℚ.+ (δ ℚ.+ δ) ≡ ε
      ι =
        ((δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))) ℚ.+ (δ ℚ.+ δ)
          ≡⟨ sym $ ℚ.+Assoc (δ ℚ.+ δ)
                            ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)) (δ ℚ.+ δ) ⟩
        (δ ℚ.+ δ) ℚ.+ (((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ)) ℚ.+ (δ ℚ.+ δ))
           ≡⟨ cong (ℚ._+_ (δ ℚ.+ δ))
                   (sym $ ℚ.+Assoc (θ ℚ.+ (δ ℚ.+ δ)) (δ ℚ.+ δ) (δ ℚ.+ δ)) ⟩
        (δ ℚ.+ δ) ℚ.+ ((θ ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)))
           ≡⟨ cong (ℚ._+_ (δ ℚ.+ δ))
                   (sym $ ℚ.+Assoc θ (δ ℚ.+ δ) ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))) ⟩
        (δ ℚ.+ δ) ℚ.+ (θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))))
           ≡⟨ ℚ.addRightSwap (δ ℚ.+ δ) θ
                             ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))) ⟩
        θ ℚ.+ ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))))
          ≡⟨ cong (ℚ._+_ θ)
                  (ℚ.+Assoc (δ ℚ.+ δ) (δ ℚ.+ δ) ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ))) ⟩
        θ ℚ.+ (((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)) ℚ.+ ((δ ℚ.+ δ) ℚ.+ (δ ℚ.+ δ)))
          ≡⟨ cong (ℚ._+_ θ) η₃ ⟩
        θ ℚ.+ (ε ℚ.- θ)
          ≡⟨ ℚ.addLeftSubtractCancel θ ε ⟩
        ε ∎

      ζ₃ : Σ (0 ℚ.< ε) (λ p → Close ε p (limit x φ) (limit y ψ))
      ζ₃ = subst (λ e → Σ (0 ℚ.< e) (λ p → Close e p (limit x φ) (limit y ψ)))
                 ι (_ , ζ₂)

      ζ₄ : limit x φ ∼[ ε , χ ] limit y ψ
      ζ₄ = subst (λ p → Close ε p (limit x φ) (limit y ψ))
                 (ℚ.isProp< 0 ε (fst ζ₃) χ) (snd ζ₃)

  pProposition : (x y : ℝ) → isProp (P x y)
  pProposition x y = isPropΠ3 (λ ε φ ψ → squash ε φ x y)

maxAddLeft : (a x y : ℝ) →
  max (a + x) (a + y) ≡ a + max x y
maxAddLeft =
  continuousExtensionLaw₃ f g f' g' φ ψ ω χ π ρ σ τ υ
  where
  f : ℝ → ℝ → ℝ → ℝ
  f a x y = max (a + x) (a + y)

  g : ℝ → ℝ → ℝ → ℝ
  g a x y = a + max x y

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' a x y = ℚ.max (a ℚ.+ x) (a ℚ.+ y)

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' a x y = a ℚ.+ ℚ.max x y

  α : (q r : ℚ.ℚ) → rational q + rational r ≡ rational (q ℚ.+ r)
  α = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

  β : (q r : ℚ.ℚ) → max (rational q) (rational r) ≡ rational (ℚ.max q r)
  β = liftNonexpanding₂≡rational ℚ.max maxNonexpandingℚ₂

  φ : (a x y : ℚ.ℚ) →
      f (rational a) (rational x) (rational y) ≡ rational (f' a x y)
  φ a x y =
    max (rational a + rational x) (rational a + rational y)
      ≡⟨ cong₂ max (α a x) (α a y) ⟩
    max (rational (a ℚ.+ x)) (rational (a ℚ.+ y))
      ≡⟨ β (a ℚ.+ x) (a ℚ.+ y) ⟩
    rational (ℚ.max (a ℚ.+ x) (a ℚ.+ y)) ∎

  ψ : (a x y : ℚ.ℚ) →
      g (rational a) (rational x) (rational y) ≡ rational (g' a x y)
  ψ a x y =
    rational a + max (rational x) (rational y)
      ≡⟨ cong (rational a +_) (β x y) ⟩
    rational a + rational (ℚ.max x y)
      ≡⟨ α a (ℚ.max x y) ⟩
    rational (a ℚ.+ ℚ.max x y) ∎

  ω : (a x y : ℚ.ℚ) → f' a x y ≡ g' a x y
  ω a x y = ℚ.maxAddLeft a x y

  χ : (a x : ℝ) → Continuous (f a x)
  χ a x = continuousCompose
            (a +_) (max (a + x))
            (+continuous₂ a) (maxContinuous₂ (a + x))

  π : (a y : ℝ) → Continuous (λ x → f a x y)
  π a y = continuousCompose
            (a +_) (flip max (a + y))
            (+continuous₂ a) (maxContinuous₁ (a + y))

  ρ : (x y : ℝ) → Continuous (λ a → f a x y)
  ρ x y = lipschitz→continuous (λ a → f a x y) 2 ℚ.0<2
            (lipschitz₂-composeLipschitz₁-lipschitz
              1 1 1 1 ℚ.0<1 ℚ.0<1 ℚ.0<1 ℚ.0<1
              (+lipschitz₁ x) (+lipschitz₁ y) maxLipschitz₁ maxLipschitz₂)

  σ : (a x : ℝ) → Continuous (g a x)
  σ a x = continuousCompose
            (max x) (a +_)
            (maxContinuous₂ x) (+continuous₂ a)

  τ : (a y : ℝ) → Continuous (λ x → g a x y)
  τ a y = continuousCompose
            (flip max y) (a +_)
            (maxContinuous₁ y) (+continuous₂ a)

  υ : (x y : ℝ) → Continuous (λ a → g a x y)
  υ x y = +continuous₁ (max x y)

maxAddRight :
  (a x y : ℝ) → max (x + a) (y + a) ≡ max x y + a
maxAddRight a x y =
  max (x + a) (y + a)
    ≡⟨ cong₂ max (+-commutative x a) (+-commutative y a) ⟩
  max (a + x) (a + y)
    ≡⟨ maxAddLeft a x y ⟩
  a + max x y
    ≡⟨ +-commutative a (max x y) ⟩
  max x y + a ∎

addLeftMonotone : {x y a : ℝ} → x ≤ y → a + x ≤ a + y
addLeftMonotone {x} {y} {a} φ =
  max (a + x) (a + y)
    ≡⟨ maxAddLeft a x y ⟩
  a + max x y
    ≡⟨ cong (_+_ a) φ ⟩
  a + y ∎

addRightMonotone : {x y a : ℝ} → x ≤ y → x + a ≤ y + a
addRightMonotone {x} {y} {a} φ =
  max (x + a) (y + a)
    ≡⟨ cong₂ max (+-commutative x a) (+-commutative y a) ⟩
  max (a + x) (a + y)
    ≡⟨ addLeftMonotone {x = x} {y = y} {a = a} φ ⟩
  a + y
    ≡⟨ +-commutative a y ⟩
  y + a ∎

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
    υ' = ℚ.0</ {x = ℚ.min δ₁ δ₂} {y = 2} υ ℚ.0<2

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
  limitCase x φ ψ ε ω = {!!}
    where
    δ : ℚ.ℚ
    δ = ε / 5 [ ℚ.5≠0 ]

    χ : 0 ℚ.< δ
    χ = {!!}

    π : x δ χ < x δ χ + rational δ
    π = {!!}

    ρ : x δ χ ∼[ δ ℚ.+ δ , {ℚ.0<+' {x = ?} {y = ?} ? ?} ] limit x φ
    ρ = {!!}

    σ : limit x φ < x δ χ + rational (δ ℚ.+ δ ℚ.+ δ)
    σ = {!!}

    τ : (limit x φ < limit x φ + rational ε) ⊔′
        (limit x φ + rational ε < x δ χ + rational (δ ℚ.+ δ ℚ.+ δ))
    τ = {!!}

    υ : ¬ (limit x φ + rational ε < x δ χ + rational (δ ℚ.+ δ ℚ.+ δ))
    υ = {!!}

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

addLeftStrictMonotone : {x y a : ℝ} → x < y → a + x < a + y
addLeftStrictMonotone {x} {y} {a} φ = {!!}

addRightStrictMonotone : {x y a : ℝ} → x < y → x + a < y + a
addRightStrictMonotone {x} {y} {a} φ = ψ'
  where
  ψ : a + x < a + y
  ψ = addLeftStrictMonotone {x} {y} {a} φ

  ψ' : x + a < y + a
  ψ' = subst2 _<_ (+-commutative a x) (+-commutative a y) ψ

-- HoTT Exercise 11.8

lipschitzClosedInterval→composeClampLipschitz :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  ((ε : ℚ.ℚ) (ω : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ ω ] f r) →
  Lipschitzℚ (f ∘ ℚ.clamp a b φ) L ψ
lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω q s ε π ρ = τ
  where
  σ : ℚ.distance (ℚ.max a (ℚ.min q b)) (ℚ.max a (ℚ.min s b)) ℚ.≤
        ℚ.distance (ℚ.min q b) (ℚ.min s b)
  σ = ℚ.maxNonexpandingʳ a (ℚ.min q b) (ℚ.min s b)

  σ' : ℚ.distance (ℚ.min q b) (ℚ.min s b) ℚ.≤ ℚ.distance q s
  σ' = ℚ.minNonexpandingˡ q s b

  σ'' : ℚ.distance (ℚ.clamp' a b φ q) (ℚ.clamp' a b φ s) ℚ.< ε
  σ'' = ℚ.isTrans≤<
          (ℚ.distance (ℚ.clamp' a b φ q) (ℚ.clamp' a b φ s))
          (ℚ.distance q s)
          ε
          (ℚ.isTrans≤
            (ℚ.distance (ℚ.clamp' a b φ q) (ℚ.clamp' a b φ s))
            (ℚ.distance (ℚ.min q b) (ℚ.min s b))
            (ℚ.distance q s)
            σ σ')
          ρ

  τ : f (ℚ.clamp a b φ q)
      ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ π ]
      f (ℚ.clamp a b φ s)
  τ = ω ε π (ℚ.clamp a b φ q) (ℚ.clamp a b φ s) σ''

liftLipschitzClosedInterval :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  ((ε : ℚ.ℚ) (ω : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ ω ] f r) →
  Σ ℝ (λ x → (rational a ≤ x) × (x ≤ rational b)) → ℝ
liftLipschitzClosedInterval a b φ f L ψ ω =
  liftLipschitz
    (f ∘ ℚ.clamp a b φ)
    L ψ
    (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω) ∘
  fst

liftLipschitzClosedIntervalLipschitz :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  (ω : (ε : ℚ.ℚ) (χ : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ χ ] f r) →
  ((ε : ℚ.ℚ) (χ : 0 ℚ.< ε)
   (x y : Σ ℝ (λ x → (rational a ≤ x) × (x ≤ rational b))) →
   fst x ∼[ ε , χ ] fst y →
   (liftLipschitzClosedInterval a b φ f L ψ ω) x
   ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ χ ]
   (liftLipschitzClosedInterval a b φ f L ψ ω) y)
liftLipschitzClosedIntervalLipschitz a b φ f L ψ ω ε χ x y π =
  liftLipschitzLipschitz
    (f ∘ ℚ.clamp a b φ)
    L ψ
    (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
    (fst x) (fst y)
    ε χ
    π

liftLipschitzClosedInterval≡rational :
  (a b : ℚ.ℚ)
  (φ : a ℚ.≤ b)
  (f : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b)) → ℝ)
  (L : ℚ.ℚ) (ψ : 0 ℚ.< L) →
  (ω : (ε : ℚ.ℚ) (χ : 0 ℚ.< ε)
   (q r : Σ ℚ.ℚ (λ q → (a ℚ.≤ q) × (q ℚ.≤ b))) →
   ℚ.∣ (fst q) ℚ.- (fst r) ∣ ℚ.< ε →
   f q ∼[ L ℚ.· ε , ℚ.0<· {x = L} {y = ε} ψ χ ] f r) →
  (q : ℚ.ℚ) (χ : a ℚ.≤ q) (π : q ℚ.≤ b) →
  (liftLipschitzClosedInterval a b φ f L ψ ω)
    (rational q , (rationalMonotone {q = a} {r = q} χ ,
                   rationalMonotone {q = q} {r = b} π)) ≡
  f (q , (χ , π))
liftLipschitzClosedInterval≡rational a b φ f L ψ ω q χ π = τ
  where
  ρ : liftLipschitz
        (λ x → f (ℚ.clamp a b φ x))
           L ψ
           (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
           (rational q) ≡
        f (ℚ.clamp a b φ q)
  ρ = liftLipschitz≡rational
        (f ∘ ℚ.clamp a b φ)
           L ψ
           (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
           q

  σ : ℚ.clamp a b φ q ≡ (q , (χ , π))
  σ = ℚ.clampFstLeftInverse a b φ (q , (χ , π))

  τ : liftLipschitz (λ x → f (ℚ.clamp a b φ x)) L ψ
       (lipschitzClosedInterval→composeClampLipschitz a b φ f L ψ ω)
       (rational q) ≡
      f (q , (χ , π))
  τ = ρ ∙ cong f σ

abstract
  leftMultiplyRationalLipschitzℚ :
    (q δ : ℚ.ℚ) (φ : 0 ℚ.< δ) →
    Lipschitzℚ (rational ∘ (λ r → q ℚ.· r)) (ℚ.max ℚ.∣ q ∣ δ)
               (ℚ.isTrans<≤ 0 δ (ℚ.max ℚ.∣ q ∣ δ) φ (ℚ.≤max' ℚ.∣ q ∣ δ))
  leftMultiplyRationalLipschitzℚ q δ φ r s ε ψ ω =
    rationalRational (q ℚ.· r) (q ℚ.· s) (L ℚ.· ε) (ℚ.0<· {x = L} {y = ε} σ ψ)
      (ℚ.∣∣<→<₂ {x = (q ℚ.· r) ℚ.- (q ℚ.· s)} {ε = L ℚ.· ε} τ')
      (ℚ.∣∣<→<₁ {x = (q ℚ.· r) ℚ.- (q ℚ.· s)} {ε = L ℚ.· ε} τ')
    where
    χ : (q ℚ.· r) ℚ.- (q ℚ.· s) ≡ q ℚ.· (r ℚ.- s)
    χ = (q ℚ.· r) ℚ.- (q ℚ.· s)
          ≡⟨ cong (ℚ._+_ (q ℚ.· r)) (ℚ.-·≡·- q s) ⟩
        (q ℚ.· r) ℚ.+ (q ℚ.· (ℚ.- s))
          ≡⟨ sym (ℚ.·DistL+ q r (ℚ.- s)) ⟩
        q ℚ.· (r ℚ.- s) ∎
  
    π : ℚ.∣ q ℚ.· (r ℚ.- s) ∣ ≡ ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣
    π = ℚ.magnitudeMultiply≡multiplyMagnitude q (r ℚ.- s)
  
    π' : ℚ.∣ (q ℚ.· r) ℚ.- (q ℚ.· s) ∣ ≡ ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣
    π' = ℚ.∣ (q ℚ.· r) ℚ.- (q ℚ.· s) ∣
           ≡⟨ cong ℚ.∣_∣ χ  ⟩
         ℚ.∣ q ℚ.· (r ℚ.- s) ∣
           ≡⟨ π ⟩
         ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣ ∎
  
    L : ℚ.ℚ
    L = ℚ.max ℚ.∣ q ∣ δ
  
    ρ : ℚ.∣ q ∣ ℚ.≤ L
    ρ = ℚ.≤max ℚ.∣ q ∣ δ
  
    ρ' : δ ℚ.≤ L
    ρ' = ℚ.≤max' ℚ.∣ q ∣ δ
  
    σ : 0 ℚ.< L
    σ = ℚ.isTrans<≤ 0 δ L φ ρ'
  
    τ : ℚ.∣ q ∣ ℚ.· ℚ.∣ r ℚ.- s ∣ ℚ.< L ℚ.· ε
    τ = ℚ.≤→<→·<· {x = ℚ.∣ q ∣} {y = ℚ.∣ r ℚ.- s ∣} {z = L} {w = ε}
          ρ ω
          σ (ℚ.0≤∣∣ $ r ℚ.- s)
  
    τ' : ℚ.∣ (q ℚ.· r) ℚ.- (q ℚ.· s) ∣ ℚ.< L ℚ.· ε
    τ' = subst (ℚ._< (L ℚ.· ε)) (sym π') τ

leftMultiplyRational : 
  ℚ.ℚ → ℝ → ℝ
leftMultiplyRational q =
  liftLipschitz
    (rational ∘ λ r → q ℚ.· r)
    (ℚ.max ℚ.∣ q ∣ 1)
    (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
    (leftMultiplyRationalLipschitzℚ q 1 ℚ.0<1)

leftMultiplyRationalLipschitzℝ :
  (q : ℚ.ℚ) →
  Lipschitzℝ
    (leftMultiplyRational q)
    (ℚ.max ℚ.∣ q ∣ 1)
    (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
leftMultiplyRationalLipschitzℝ q =
  let
    -- Again, I don't know why Agda is so weird
    φ = liftLipschitzLipschitz
          (λ r → rational (q ℚ.· r))
          (ℚ.max ℚ.∣ q ∣ 1)
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
          (leftMultiplyRationalLipschitzℚ q 1 ℚ.0<1)
  in φ

leftMultiplyRationalContinuous :
  (q : ℚ.ℚ) →
  Continuous $ leftMultiplyRational q
leftMultiplyRationalContinuous q =
  lipschitz→continuous
    (leftMultiplyRational q)
    (ℚ.max ℚ.∣ q ∣ 1)
    _
    (leftMultiplyRationalLipschitzℝ q)

distanceLeftMultiplyRational≡leftMultiplyRationalDistance :
  (q r : ℚ.ℚ)
  (y : ℝ) →
  distance (leftMultiplyRational q y) (leftMultiplyRational r y) ≡
  leftMultiplyRational (ℚ.distance q r) ∣ y ∣
distanceLeftMultiplyRational≡leftMultiplyRationalDistance q r =
  continuousExtensionLaw₁ f g f' g' φ ψ ω χ π
  where
  f : ℝ → ℝ
  f y = distance (leftMultiplyRational q y) (leftMultiplyRational r y)

  g : ℝ → ℝ
  g y = leftMultiplyRational (ℚ.distance q r) ∣ y ∣

  f' : ℚ.ℚ → ℚ.ℚ
  f' s = ℚ.distance (q ℚ.· s) (r ℚ.· s)

  g' : ℚ.ℚ → ℚ.ℚ
  g' s = (ℚ.distance q r) ℚ.· ℚ.∣ s ∣

  φ : (f ∘ rational) ∼ (rational ∘ f')
  φ s = refl

  ψ : (g ∘ rational) ∼ (rational ∘ g')
  ψ s = refl

  ω : f' ∼ g'
  ω s = ℚ.·distanceᵣ s q r

  χ : Continuous f
  χ = lipschitz→continuous
           (λ x → distance (leftMultiplyRational q x)
                           (leftMultiplyRational r x))
           (1 ℚ.· (ℚ.max ℚ.∣ q ∣ 1) ℚ.+ 1 ℚ.· (ℚ.max ℚ.∣ r ∣ 1))
           _
           π
    where
    π : Lipschitzℝ
         (λ x → distance (leftMultiplyRational q x)
                         (leftMultiplyRational r x))
         (1 ℚ.· ℚ.max ℚ.∣ q ∣ 1 ℚ.+ 1 ℚ.· ℚ.max ℚ.∣ r ∣ 1)
         _
    π = lipschitz₂-composeLipschitz₁-lipschitz
          (ℚ.max ℚ.∣ q ∣ 1) (ℚ.max ℚ.∣ r ∣ 1)
          1 1
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ q ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ q ∣ 1))
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ r ∣ 1) ℚ.0<1 (ℚ.≤max' ℚ.∣ r ∣ 1))
          ℚ.0<1 ℚ.0<1
          (leftMultiplyRationalLipschitzℝ q)
          (leftMultiplyRationalLipschitzℝ r)
          (nonexpandingℝ₂→lipschitzℝ₁ distance distanceNonexpandingℝ₂)
          (nonexpandingℝ₂→lipschitzℝ₂ distance distanceNonexpandingℝ₂)

  π : Continuous g
  π = lipschitz→continuous
        (leftMultiplyRational (ℚ.distance q r) ∘ ∣_∣)
        (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1 ℚ.· 2)
        _
        ρ
    where
    ρ : Lipschitzℝ (leftMultiplyRational (ℚ.distance q r) ∘ ∣_∣)
          (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1 ℚ.· 2) _
    ρ = lipschitzCompose
          (leftMultiplyRational (ℚ.distance q r))
          ∣_∣
          (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1) 2
          (ℚ.isTrans<≤ 0 1 (ℚ.max ℚ.∣ ℚ.distance q r ∣ 1) ℚ.0<1
            (ℚ.≤max' ℚ.∣ ℚ.distance q r ∣ 1))
          ℚ.0<2
          (leftMultiplyRationalLipschitzℝ (ℚ.distance q r))
          magnitudeLipschitzℝ

maxLeftMultiplyRationalNonnegative :
  (q : ℚ.ℚ)
  (φ : 0 ℚ.≤ q) →
  (x y : ℝ) →
  max (leftMultiplyRational q x) (leftMultiplyRational q y) ≡
  leftMultiplyRational q (max x y)
maxLeftMultiplyRationalNonnegative q φ =
  continuousExtensionLaw₂ f g f' g' ψ ω χ π ρ σ τ
  where
  f : ℝ → ℝ → ℝ
  f x y = max (leftMultiplyRational q x) (leftMultiplyRational q y)

  g : ℝ → ℝ → ℝ
  g x y = leftMultiplyRational q (max x y)

  f' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  f' s t = ℚ.max (q ℚ.· s) (q ℚ.· t)

  g' : ℚ.ℚ → ℚ.ℚ → ℚ.ℚ
  g' s t = q ℚ.· ℚ.max s t

  ψ : (s t : ℚ.ℚ) → f (rational s) (rational t) ≡ rational (f' s t)
  ψ s t = refl

  ω : (s t : ℚ.ℚ) → g (rational s) (rational t) ≡ rational (g' s t)
  ω s t = refl

  χ : (s t : ℚ.ℚ) → f' s t ≡ g' s t
  χ s t = ℚ.maxMultiplyLeftNonnegative q s t φ

  π : (u : ℝ) → Continuous (f u)
  π u = continuousCompose
          (leftMultiplyRational q)
          (max (leftMultiplyRational q u))
          (leftMultiplyRationalContinuous q)
          (maxContinuous₂ (leftMultiplyRational q u))

  ρ : (v : ℝ) → Continuous (flip f v)
  ρ v = continuousCompose
          (leftMultiplyRational q)
          (flip max (leftMultiplyRational q v))
          (leftMultiplyRationalContinuous q)
          (maxContinuous₁ (leftMultiplyRational q v))

  σ : (u : ℝ) → Continuous (g u)
  σ u = continuousCompose
          (max u)
          (leftMultiplyRational q)
          (maxContinuous₂ u)
          (leftMultiplyRationalContinuous q)

  τ : (v : ℝ) → Continuous (flip g v)
  τ v = continuousCompose
          (flip max v)
          (leftMultiplyRational q)
          (maxContinuous₁ v)
          (leftMultiplyRationalContinuous q)

leftMultiplyRationalNonnegativeMonotone :
  (q : ℚ.ℚ)
  (φ : 0 ℚ.≤ q) →
  (x y : ℝ) →
  x ≤ y → leftMultiplyRational q x ≤ leftMultiplyRational q y
leftMultiplyRationalNonnegativeMonotone q φ x y ψ =
  max (leftMultiplyRational q x) (leftMultiplyRational q y)
    ≡⟨ maxLeftMultiplyRationalNonnegative q φ x y ⟩
  leftMultiplyRational q (max x y)
    ≡⟨ cong (leftMultiplyRational q) ψ ⟩
  leftMultiplyRational q y ∎

leftMultiplyRationalLipschitzℚ₁ :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) →
  ∣ y ∣ ≤ rational L →
  Lipschitzℚ (λ q → leftMultiplyRational q y) L φ
leftMultiplyRationalLipschitzℚ₁ L φ y ψ q r ε ω χ =
  υ
  where
  π : distance (leftMultiplyRational q y) (leftMultiplyRational r y) ≡
      leftMultiplyRational (ℚ.distance q r) ∣ y ∣
  π = distanceLeftMultiplyRational≡leftMultiplyRationalDistance q r y

  ρ : leftMultiplyRational (ℚ.distance q r) ∣ y ∣ ≤
      leftMultiplyRational (ℚ.distance q r) (rational L)
  ρ = leftMultiplyRationalNonnegativeMonotone
        (ℚ.distance q r)
        (ℚ.0≤∣∣ $ q ℚ.- r)
        ∣ y ∣ (rational L)
        ψ

  σ : (ℚ.distance q r) ℚ.· L ℚ.< ε ℚ.· L
  σ = ℚ.<-·o (ℚ.distance q r) ε L φ χ

  σ' : (ℚ.distance q r) ℚ.· L ℚ.< L ℚ.· ε
  σ' = subst (λ ?x → (ℚ.distance q r) ℚ.· L ℚ.< ?x) (ℚ.·Comm ε L) σ

  τ : leftMultiplyRational (ℚ.distance q r) ∣ y ∣ < rational (L ℚ.· ε)
  τ = ≤→<→< {x = leftMultiplyRational (ℚ.distance q r) ∣ y ∣}
        ρ (rationalStrictMonotone {q = (ℚ.distance q r) ℚ.· L} σ')

  τ' : distance (leftMultiplyRational q y) (leftMultiplyRational r y) <
       rational (L ℚ.· ε)
  τ' = subst (λ ?x → ?x < rational (L ℚ.· ε)) (sym π) τ

  υ : Close (L ℚ.· ε) (ℚ.0<· {x = L} {y = ε} φ ω)
            (leftMultiplyRational q y) (leftMultiplyRational r y)
  υ = distance<→close (ℚ.0<· {x = L} {y = ε} φ ω) τ'

boundedMultiply :
  (L : ℚ.ℚ) (φ : 0 ℚ.< L)
  (y : ℝ) →
  ∣ y ∣ ≤ rational L →
  ℝ → ℝ
boundedMultiply L φ y ψ =
  liftLipschitz
    (λ q → leftMultiplyRational q y)
    L φ
    (leftMultiplyRationalLipschitzℚ₁ L φ y ψ)

-- Gilbert Lemma 4.13: Cauchy reals are bounded by rationals
∣∣<rational :
  (x : ℝ) → ∃ ℚ.ℚ (λ q → (0 ℚ.< q) × (∣ x ∣ < rational q))
∣∣<rational x = ∃-rec isPropPropTrunc χ ω
  where
  φ : 0 < 1
  φ = rationalStrictMonotone {q = 0} {r = 1} ℚ.0<1

  ψ : ∣ x ∣ < ∣ x ∣ + 1
  ψ = subst (λ y → y < ∣ x ∣ + 1)
            (+-unitʳ ∣ x ∣)
            (addLeftStrictMonotone {x = 0} {y = 1} {a = ∣ x ∣} φ)

  ω : ∃ ℚ.ℚ (λ q → (∣ x ∣ < rational q) × (rational q < ∣ x ∣ + 1))
  ω = <-archimedian ∣ x ∣ (∣ x ∣ + 1) ψ

  χ : (q : ℚ.ℚ) →
      (∣ x ∣ < rational q) × (rational q < ∣ x ∣ + 1) →
      ∃ ℚ.ℚ (λ r → (0 ℚ.< r) × (∣ x ∣ < rational r))
  χ q (π , _) = ∣ q , (ρ' , π) ∣₁
    where
    ρ : 0 < rational q
    ρ = ≤→<→< {x = 0} {y = ∣ x ∣} {z = rational q} (0≤magnitude x) π

    ρ' : 0 ℚ.< q
    ρ' = rationalStrictReflective {q = 0} {r = q} ρ
