module HoTTReals.Data.Real.Algebra.Addition where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Data.Nat.Literals public
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Homotopy.Base

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

open import HoTTReals.Data.Real.Algebra.Negation

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

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

+rational : (q r : ℚ.ℚ) →
  rational q + rational r ≡ rational (q ℚ.+ r)
+rational = liftNonexpanding₂≡rational ℚ._+_ +nonexpandingℚ₂

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
