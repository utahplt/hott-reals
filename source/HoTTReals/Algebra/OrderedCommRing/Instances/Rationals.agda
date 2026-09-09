module HoTTReals.Algebra.OrderedCommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.Algebra.OrderedCommRing.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals using (ℚ!)

open PositiveRationals
open ℚ₊Inverse
open OrderedCommRingTheory ℚOrderedCommRing using (·MonoL≤)

⁻¹₊Flip≤ : {δ ε : ℚ₊} → δ ≤₊ ε → ε ⁻¹₊ ≤₊ δ ⁻¹₊
⁻¹₊Flip≤ {δ} {ε} δ≤ε = {!!}
