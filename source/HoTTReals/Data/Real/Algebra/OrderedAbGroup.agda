module HoTTReals.Data.Real.Algebra.OrderedAbGroup where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition

ℝOrderedAbGroup : OrderedAbGroup ℓ-zero ℓ-zero
fst ℝOrderedAbGroup = ℝ
OrderedAbGroupStr.0g (snd ℝOrderedAbGroup) = 0
OrderedAbGroupStr._+_ (snd ℝOrderedAbGroup) = _+_
OrderedAbGroupStr.-_ (snd ℝOrderedAbGroup) = -_
OrderedAbGroupStr._<_ (snd ℝOrderedAbGroup) = _<_
OrderedAbGroupStr._≤_ (snd ℝOrderedAbGroup) = _≤_
OrderedAbGroupStr.isOrderedAbGroup (snd ℝOrderedAbGroup) = isOrderedAbGroupℝ
  where
  isOrderedAbGroupℝ : IsOrderedAbGroup 0 _+_ -_ _<_ _≤_
  IsOrderedAbGroup.isAbGroup isOrderedAbGroupℝ =
    AbGroupStr.isAbGroup (snd ℝAbGroup)
  IsOrderedAbGroup.isPseudolattice isOrderedAbGroupℝ =
    PseudolatticeStr.is-pseudolattice (snd ℝ≤Pseudolattice)
  IsOrderedAbGroup.isStrictOrder isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.<-≤-weaken isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.≤≃¬> isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.+MonoR≤ isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.+MonoR< isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.posSum→pos∨pos isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.<-≤-trans isOrderedAbGroupℝ = {!!}
  IsOrderedAbGroup.≤-<-trans isOrderedAbGroupℝ = {!!}
