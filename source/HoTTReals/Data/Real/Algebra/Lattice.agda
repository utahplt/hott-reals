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
open import HoTTReals.Relation.Premetric.Instances.Product
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
minⁿ = liftNE₂ ((ratⁿ Q.ⁿ∘ⁿ-) ∘NE ℚ.minⁿ)

min : ℝ → ℝ → ℝ
min = fst ∘ (fst minⁿ)

minNE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
minNE₂ = NE→NE₂ _ _ _ minⁿ

[_]minⁿ : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
[ x ]minⁿ = min x , NE₂[_,_,_].rNE minNE₂ x

minⁿ[_] : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
minⁿ[ x ] = flip min x , NE₂[_,_,_].lNE minNE₂ x

maxⁿ : NE[ ℝPremetricSpace , NE[ ℝPremetricSpace , ℝPremetricSpace ]PrSpace ]
maxⁿ = liftNE₂ ((ratⁿ Q.ⁿ∘ⁿ-) ∘NE ℚ.maxⁿ)

max : ℝ → ℝ → ℝ
max = fst ∘ (fst maxⁿ)

maxNE₂ : NE₂[ ℝPremetricSpace , ℝPremetricSpace , ℝPremetricSpace ]
maxNE₂ = NE→NE₂ _ _ _ maxⁿ

[_]maxⁿ : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
[ x ]maxⁿ = max x , NE₂[_,_,_].rNE maxNE₂ x

maxⁿ[_] : ℝ → NE[ ℝPremetricSpace , ℝPremetricSpace ]
maxⁿ[ x ] = flip max x , NE₂[_,_,_].lNE maxNE₂ x

minComm : (x y : ℝ) → min x y ≡ min y x
minComm =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( minⁿ)
    ( flipNE minⁿ)
    ( λ q r → cong rat (ℚ.minComm q r))

maxComm : (x y : ℝ) → max x y ≡ max y x
maxComm =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( maxⁿ)
    ( flipNE maxⁿ)
    ( λ q r → cong rat (ℚ.maxComm q r))

maxIdem : (x : ℝ) → max x x ≡ x
maxIdem =
  lipschitz≡
    ( _)
    ( _)
    ( composeNE₂ _ _ _ idⁿ idⁿ maxNE₂)
    ( idᴸ)
    ( cong rat ∘ ℚ.maxIdem)

minAssoc : (x y z : ℝ) → min x (min y z) ≡ min (min x y) z
minAssoc x =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( ([ x ]minⁿ R.ⁿ∘ⁿ-) ∘NE minⁿ)
    ( minⁿ ∘NE [ x ]minⁿ)
    ( λ r s →
      nonExpansive≡
        ( _)
        ( _)
        ( minⁿ[ min (rat r) (rat s) ])
        ( minⁿ[ rat s ] ∘NE minⁿ[ rat r ])
        ( λ q → cong rat (ℚ.minAssoc q r s))
        ( x))

maxAssoc : (x y z : ℝ) → max x (max y z) ≡ max (max x y) z
maxAssoc x =
  nonExpansive₂≡
    ( _)
    ( _)
    ( _)
    ( ([ x ]maxⁿ R.ⁿ∘ⁿ-) ∘NE maxⁿ)
    ( maxⁿ ∘NE [ x ]maxⁿ)
    ( λ r s →
      nonExpansive≡
        ( _)
        ( _)
        ( maxⁿ[ max (rat r) (rat s) ])
        ( maxⁿ[ rat s ] ∘NE maxⁿ[ rat r ])
        ( λ q → cong rat (ℚ.maxAssoc q r s))
        ( x))

minAbsorbLMax : (x y : ℝ) → min x (max x y) ≡ x
minAbsorbLMax x =
  nonExpansive≡
    ( _)
    ( _)
    ( [ x ]minⁿ ∘NE [ x ]maxⁿ)
    ( constⁿ x)
    ( λ r →
      lipschitz≡
        ( _)
        ( _)
        ( composeNE₂ _ _ _ idⁿ maxⁿ[ rat r ] minNE₂)
        ( idᴸ)
        ( λ q → cong rat (ℚ.minAbsorbLMax q r))
        ( x))

maxAbsorbLMin : (x y : ℝ) → max x (min x y) ≡ x
maxAbsorbLMin x =
  nonExpansive≡
    ( _)
    ( _)
    ( [ x ]maxⁿ ∘NE [ x ]minⁿ)
    ( constⁿ x)
    ( λ r →
      lipschitz≡
        ( _)
        ( _)
        ( composeNE₂ _ _ _ idⁿ minⁿ[ rat r ] maxNE₂)
        ( idᴸ)
        ( λ q → cong rat (ℚ.maxAbsorbLMin q r))
        ( x))

minAbsorbRMax : (x y : ℝ) → min (max x y) x ≡ x
minAbsorbRMax x y = minComm (max x y) x ∙ minAbsorbLMax x y

maxAbsorbRMin : (x y : ℝ) → max (min x y) x ≡ x
maxAbsorbRMin x y = maxComm (min x y) x ∙ maxAbsorbLMin x y
