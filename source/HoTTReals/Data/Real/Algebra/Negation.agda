module HoTTReals.Data.Real.Algebra.Negation where

import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat.Literals public

open import HoTTReals.Data.Real.Base
open import HoTTReals.Data.Real.Close
open import HoTTReals.Data.Real.Definitions
open import HoTTReals.Data.Real.Induction
open import HoTTReals.Data.Real.Lipschitz.Base
open import HoTTReals.Data.Real.Nonexpanding
open import HoTTReals.Data.Real.Properties

import HoTTReals.Data.Rationals.Order as ℚ
import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Logic

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
