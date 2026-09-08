module HoTTReals.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import HoTTReals.Algebra.OrderedField.Base

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField =
  ℚ , orderedfieldstr 0 1 ℚ._+_ ℚ._·_ ℚ.-_ ℚ._<_ ℚ._≤_ isOrderedFieldℚ
  where
  isOrderedFieldℚ : IsOrderedField 0 1 ℚ._+_ ℚ._·_ ℚ.-_ ℚ._<_ ℚ._≤_
  IsOrderedField.isOrderedCommRing isOrderedFieldℚ = {!!}
  IsOrderedField.#0→isInv isOrderedFieldℚ = {!!}
  IsOrderedField.isInv→#0 isOrderedFieldℚ = {!!}
