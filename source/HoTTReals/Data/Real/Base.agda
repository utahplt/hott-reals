module HoTTReals.Data.Real.Base where

open import Cubical.Data.Bool as Bool using ()
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Surjection
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation

open import HoTTReals.Algebra.Field.Instances.Rationals as ℚ
open import HoTTReals.Data.Rationals.Order as ℚ
open import HoTTReals.Data.Rationals.Properties as ℚ
open import HoTTReals.Logic

-- HoTT Definition 11.3.2

data ℝ : Type

data Close : (ε : ℚ) → (0 < ε) → ℝ → ℝ → Type ℓ-zero

syntax Close ε p x y = x ∼[ ε , p ] y

-- HoTT Definition 11.2.10
CauchyApproximation : ((ε : ℚ) → 0 < ε → ℝ) → Type ℓ-zero
CauchyApproximation x =
  ((δ ε : ℚ) (p : 0 < δ) (q : 0 < ε) →
   x δ p ∼[ δ + ε , 0<+' {x = δ} {y = ε} p q ] x ε q)

data ℝ where
  rational : ℚ → ℝ
  limit : (x : (ε : ℚ) → 0 < ε → ℝ) →
          CauchyApproximation x →
          ℝ
  path : (x y : ℝ) →
         ((ε : ℚ) (p : 0 < ε) → x ∼[ ε , p ] y) →
         x ≡ y

data Close where
  rationalRational :
    (q r ε : ℚ) (φ : 0 < ε) →
    - ε < q - r → q - r < ε →
    rational q ∼[ ε , φ ] rational r
  rationalLimit :
    (q ε δ : ℚ) (φ : 0 < ε) (ψ : 0 < δ) (θ : 0 < ε - δ)
    (y : (ε : ℚ) → 0 < ε → ℝ) (ω : CauchyApproximation y) →
    rational q ∼[ ε - δ , θ ] (y δ ψ) →
    rational q ∼[ ε , φ ] (limit y ω)
  limitRational :
    (x : (ε : ℚ) → 0 < ε → ℝ) (φ : CauchyApproximation x)
    (r ε δ : ℚ) (ψ : 0 < ε) (θ : 0 < δ) (ω : 0 < ε - δ) →
    (x δ θ) ∼[ ε - δ , ω ] rational r →
    limit x φ ∼[ ε , ψ ] rational r 
  limitLimit :
    (x y : (ε : ℚ) → 0 < ε → ℝ)
    (φ : CauchyApproximation x) (ψ : CauchyApproximation y)
    (ε δ η : ℚ) (θ : 0 < ε) (ω : 0 < δ) (π : 0 < η) (ρ : 0 < ε - (δ + η)) →
    (x δ ω) ∼[ ε - (δ + η) , ρ ] (y η π) →
    limit x φ ∼[ ε , θ ] limit y ψ
  squash :
    (ε : ℚ) (φ : 0 < ε) (u v : ℝ) → isProp $ u ∼[ ε , φ ] v
