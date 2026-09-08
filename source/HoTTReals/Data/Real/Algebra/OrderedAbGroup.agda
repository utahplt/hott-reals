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
  IsOrderedAbGroup.isStrictOrder isOrderedAbGroupℝ =
    StrictOrderStr.isStrictOrder (snd ℝ<StrictOrder)
  IsOrderedAbGroup.<-≤-weaken isOrderedAbGroupℝ = λ x y → <Weaken≤ {x} {y}
  IsOrderedAbGroup.≤≃¬> isOrderedAbGroupℝ = λ x y → ≤≃¬> {x} {y}
  IsOrderedAbGroup.+MonoR≤ isOrderedAbGroupℝ = λ x y z → +MonoR≤ {x} {y} {z}
  IsOrderedAbGroup.+MonoR< isOrderedAbGroupℝ = λ x y z → +MonoR< {x} {y} {z}
  IsOrderedAbGroup.posSum→pos∨pos isOrderedAbGroupℝ =
    λ x y → posSum→pos∨pos {x} {y}
  IsOrderedAbGroup.<-≤-trans isOrderedAbGroupℝ =
    λ x y z → isTrans<≤ {x} {y} {z}
  IsOrderedAbGroup.≤-<-trans isOrderedAbGroupℝ =
    λ x y z → isTrans≤< {x} {y} {z}
