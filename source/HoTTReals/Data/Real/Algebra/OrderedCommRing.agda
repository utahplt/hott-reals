module HoTTReals.Data.Real.Algebra.OrderedCommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals as ℝ hiding (
  _+_ ; -_)

open import HoTTReals.Data.Real.Algebra.Addition as ℝ
open import HoTTReals.Data.Real.Algebra.Multiplication as ℝ hiding (_·_)
open import HoTTReals.Data.Real.Order.Base as ℝ hiding (_<_ ; _≤_ ; 0<1)
open import HoTTReals.Data.Real.Order.Addition as ℝ hiding (
  ≤≃¬> ; +MonoR≤ ; +MonoR< ; posSum→pos∨pos)
import HoTTReals.Data.Real.Order.Multiplication as ℝ

open OrderedCommRingStr

ℝOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℝOrderedCommRing = ℝ
0r  (snd ℝOrderedCommRing) = 0
1r  (snd ℝOrderedCommRing) = 1
_+_ (snd ℝOrderedCommRing) = ℝ._+_
_·_ (snd ℝOrderedCommRing) = ℝ._·_
-_  (snd ℝOrderedCommRing) = ℝ.-_
_<_ (snd ℝOrderedCommRing) = ℝ._<_
_≤_ (snd ℝOrderedCommRing) = ℝ._≤_
isOrderedCommRing (snd ℝOrderedCommRing) = isOrderedCommRingℝ
  where
  open IsOrderedCommRing
  open CommRingStr      (snd ℝCommRing)       renaming (isCommRing       to isCRℝ)
  open PseudolatticeStr (snd ℝ≤Pseudolattice) renaming (is-pseudolattice to isPLℝ≤)
  open StrictOrderStr   (snd ℝ<StrictOrder)   renaming (isStrictOrder    to isSOℝ<)

  isOrderedCommRingℝ : IsOrderedCommRing _ _ _ _ _ _ _
  isOrderedCommRingℝ .isCommRing      = isCRℝ
  isOrderedCommRingℝ .isPseudolattice = isPLℝ≤
  isOrderedCommRingℝ .isStrictOrder   = isSOℝ<
  isOrderedCommRingℝ .<-≤-weaken      = λ x y   → ℝ.<Weaken≤ {x} {y}
  isOrderedCommRingℝ .≤≃¬>            = λ x y   → ℝ.≤≃¬> {x} {y}
  isOrderedCommRingℝ .+MonoR≤         = λ x y z → ℝ.+MonoR≤ {x} {y} {z}
  isOrderedCommRingℝ .+MonoR<         = λ x y z → ℝ.+MonoR< {x} {y} {z}
  isOrderedCommRingℝ .posSum→pos∨pos  = λ x y   → ℝ.posSum→pos∨pos {x} {y}
  isOrderedCommRingℝ .<-≤-trans       = λ x y z → ℝ.isTrans<≤ {x} {y} {z}
  isOrderedCommRingℝ .≤-<-trans       = λ x y z → ℝ.isTrans≤< {x} {y} {z}
  isOrderedCommRingℝ .·MonoR≤         = λ x y z → ℝ.·MonoR≤ {x} {y} {z}
  isOrderedCommRingℝ .·MonoR<         = λ x y z → ℝ.·MonoR< {x} {y} {z}
  isOrderedCommRingℝ .0<1             = ℝ.0<1
