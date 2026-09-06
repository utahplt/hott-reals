module HoTTReals.Data.Real.Algebra.Lattice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using ()

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Completion.Lift
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

import HoTTReals.Relation.Premetric.Instances.Rationals as ℚ
open import HoTTReals.Relation.Premetric.Mappings

open LiftCompleteCodomain₂
  ℚPremetricSpace
  ℚPremetricSpace
  ℝPremetricSpace
  isCompleteℝ

private
  module Q = ∘Properties ℚPremetricSpace
  module R = ∘Properties ℝPremetricSpace

minⁿ : NE[ ℝPremetricSpace , NE[ ℝPremetricSpace , ℝPremetricSpace ]PrSpace ]
minⁿ = {!!}

min : ℝ → ℝ → ℝ
min = fst ∘ (fst minⁿ)

minNE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
minNE₂ = NE→NE₂ _ _ _ minⁿ

[_]minⁿ : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
[ x ]minⁿ = min x , NE₂[_,_,_].rNE minNE₂ x

minⁿ[_] : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
minⁿ[ x ] = flip min x , NE₂[_,_,_].lNE minNE₂ x

maxⁿ : NE[ ℝPremetricSpace , NE[ ℝPremetricSpace , ℝPremetricSpace ]PrSpace ]
maxⁿ = {!!}

max : ℝ → ℝ → ℝ
max = fst ∘ (fst maxⁿ)

maxNE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
maxNE₂ = NE→NE₂ _ _ _ maxⁿ

[_]maxⁿ : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
[ x ]maxⁿ = max x , NE₂[_,_,_].rNE maxNE₂ x

maxⁿ[_] : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
maxⁿ[ x ] = flip max x , NE₂[_,_,_].lNE maxNE₂ x

minComm : (x y : ℝ) → min x y ≡ min y x
minComm = {!!}

maxComm : (x y : ℝ) → max x y ≡ max y x
maxComm = {!!}

maxIdem : (x : ℝ) → max x x ≡ x
maxIdem = {!!}

minAssoc : (x y z : ℝ) → min x (min y z) ≡ min (min x y) z
minAssoc = {!!}

maxAssoc : (x y z : ℝ) → max x (max y z) ≡ max (max x y) z
maxAssoc = {!!}

minAbsorbLMax : (x y : ℝ) → min x (max x y) ≡ x
minAbsorbLMax = {!!}

maxAbsorbLMin : (x y : ℝ) → max x (min x y) ≡ x
maxAbsorbLMin = {!!}

minAbsorbRMax : (x y : ℝ) → min (max x y) x ≡ x
minAbsorbRMax = {!!}

maxAbsorbRMin : (x y : ℝ) → max (min x y) x ≡ x
maxAbsorbRMin = {!!}
