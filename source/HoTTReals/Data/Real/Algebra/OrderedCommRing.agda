module HoTTReals.Data.Real.Algebra.OrderedCommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition
open import HoTTReals.Data.Real.Order.Multiplication

ℝOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℝOrderedCommRing = ℝ
OrderedCommRingStr.0r (snd ℝOrderedCommRing) = 0
OrderedCommRingStr.1r (snd ℝOrderedCommRing) = 1
OrderedCommRingStr._+_ (snd ℝOrderedCommRing) = _+_
OrderedCommRingStr._·_ (snd ℝOrderedCommRing) = _·_
OrderedCommRingStr.-_ (snd ℝOrderedCommRing) = -_
OrderedCommRingStr._<_ (snd ℝOrderedCommRing) = _<_
OrderedCommRingStr._≤_ (snd ℝOrderedCommRing) = _≤_
OrderedCommRingStr.isOrderedCommRing (snd ℝOrderedCommRing) = isOrderedCommRingℝ
  where
  isOrderedCommRingℝ : IsOrderedCommRing 0 1 _+_ _·_ -_ _<_ _≤_
  IsOrderedCommRing.isCommRing isOrderedCommRingℝ =
    CommRingStr.isCommRing $ snd ℝCommRing
  IsOrderedCommRing.isPseudolattice isOrderedCommRingℝ =
    PseudolatticeStr.is-pseudolattice $ snd ℝ≤Pseudolattice
  IsOrderedCommRing.isStrictOrder isOrderedCommRingℝ =
    StrictOrderStr.isStrictOrder $ snd ℝ<StrictOrder
  IsOrderedCommRing.<-≤-weaken isOrderedCommRingℝ = λ x y → <Weaken≤ {x} {y}
  IsOrderedCommRing.≤≃¬> isOrderedCommRingℝ = λ x y → ≤≃¬> {x} {y}
  IsOrderedCommRing.+MonoR≤ isOrderedCommRingℝ = λ x y z → +MonoR≤ {x} {y} {z}
  IsOrderedCommRing.+MonoR< isOrderedCommRingℝ = λ x y z → +MonoR< {x} {y} {z}
  IsOrderedCommRing.posSum→pos∨pos isOrderedCommRingℝ =
    λ x y → posSum→pos∨pos {x} {y}
  IsOrderedCommRing.<-≤-trans isOrderedCommRingℝ =
    λ x y z → isTrans<≤ {x} {y} {z}
  IsOrderedCommRing.≤-<-trans isOrderedCommRingℝ =
    λ x y z → isTrans≤< {x} {y} {z}
  IsOrderedCommRing.·MonoR≤ isOrderedCommRingℝ = λ x y z → ·MonoR≤ {x} {y} {z}
  IsOrderedCommRing.·MonoR< isOrderedCommRingℝ = λ x y z → ·MonoR< {x} {y} {z}
  IsOrderedCommRing.0<1 isOrderedCommRingℝ = 0<1
