module HoTTReals.Data.Real.Base where

open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Foundations.Prelude

open import HoTTReals.Data.Rationals.Order as ℚ

-- TODO: data type declaration

-- HoTT Definition 11.3.2

data ℝ : Type

data Equivalent-ℝ : (ε : ℚ) → (0 < ε) → ℝ → ℝ → Type

syntax Equivalent-ℝ ε p x y = x ∼[ ε , p ] y

CauchyApproximation : ((ε : ℚ) → 0 < ε → ℝ) → Type
CauchyApproximation x =
  ((δ ε : ℚ) (p : 0 < δ) (q : 0 < ε) →
   (x δ p) ∼[ δ + ε , +0< {x = δ} {y = ε} p q ] (x ε q))

data ℝ where
  rational : ℚ → ℝ
  limit : (x : (ε : ℚ) → 0 < ε → ℝ) →
          CauchyApproximation x →
          ℝ
  path : (x y : ℝ) →
         ((ε : ℚ) (p : 0 < ε) → x ∼[ ε , p ] y) →
         x ≡ y

data Equivalent-ℝ where
  rationalRational :
    (q r ε : ℚ) (p : 0 < ε) →
    - ε < q - r → q - r < ε →
    rational q ∼[ ε , p ] rational r
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
    (u v : ℝ) (ε : ℚ) (φ : 0 < ε) (ψ ψ' : u ∼[ ε , φ ] v) →
    ψ ≡ ψ'

equivalent-ℝ-reflexive : (u : ℝ) (ε : ℚ) (p : 0 < ε) → u ∼[ ε , p ] u
equivalent-ℝ-reflexive u ε p = {!!}

-- TODO: Type for lemma 1
