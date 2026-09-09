module HoTTReals.Data.Real.Algebra.OrderedField where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.HeytingField.Base
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.OrderedCommRing
open import HoTTReals.Data.Real.Algebra.Reciprocal
open import HoTTReals.Data.Real.Order.Base

ℝOrderedField : OrderedField ℓ-zero ℓ-zero
fst ℝOrderedField = ℝ
OrderedFieldStr.0f (snd ℝOrderedField) = 0
OrderedFieldStr.1f (snd ℝOrderedField) = 1
OrderedFieldStr._+_ (snd ℝOrderedField) = _+_
OrderedFieldStr._·_ (snd ℝOrderedField) = _·_
OrderedFieldStr.-_ (snd ℝOrderedField) = -_
OrderedFieldStr._<_ (snd ℝOrderedField) = _<_
OrderedFieldStr._≤_ (snd ℝOrderedField) = _≤_
OrderedFieldStr.isOrderedField (snd ℝOrderedField) = isOrderedFieldℝ
  where
  isOrderedFieldℝ : IsOrderedField 0 1 _+_ _·_ -_ _<_ _≤_
  IsOrderedField.isOrderedCommRing isOrderedFieldℝ =
    OrderedCommRingStr.isOrderedCommRing $ snd ℝOrderedCommRing
  IsOrderedField.#0→isInv isOrderedFieldℝ = #0→isInv
  IsOrderedField.isInv→#0 isOrderedFieldℝ = isInv→#0

ℝHeytingField : HeytingField ℓ-zero ℓ-zero
ℝHeytingField = OrderedField→HeytingField ℝOrderedField
