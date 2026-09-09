module HoTTReals.Data.Real.Algebra.OrderedAbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.AbGroup

open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals as ℝ hiding (
  _+_ ; -_)

open import HoTTReals.Algebra.OrderedAbGroup.Base as ℝ
open import HoTTReals.Data.Real.Algebra.Addition as ℝ
open import HoTTReals.Data.Real.Order.Base as ℝ hiding (_<_ ; _≤_ ; 0<1)
open import HoTTReals.Data.Real.Order.Addition as ℝ hiding (
  ≤≃¬> ; +MonoR≤ ; +MonoR< ; posSum→pos∨pos)

open OrderedAbGroupStr

ℝOrderedAbGroup : OrderedAbGroup ℓ-zero ℓ-zero
fst ℝOrderedAbGroup = ℝ
0g  (snd ℝOrderedAbGroup) = 0
_+_ (snd ℝOrderedAbGroup) = ℝ._+_
-_  (snd ℝOrderedAbGroup) = ℝ.-_
_<_ (snd ℝOrderedAbGroup) = ℝ._<_
_≤_ (snd ℝOrderedAbGroup) = ℝ._≤_
isOrderedAbGroup (snd ℝOrderedAbGroup) = isOrderedAbGroupℝ
  where
  open IsOrderedAbGroup
  open AbGroupStr       (snd ℝAbGroup)        renaming (isAbGroup        to isAGℝ+)
  open PseudolatticeStr (snd ℝ≤Pseudolattice) renaming (is-pseudolattice to isPLℝ≤)
  open StrictOrderStr   (snd ℝ<StrictOrder)   renaming (isStrictOrder    to isSOℝ<)

  isOrderedAbGroupℝ : IsOrderedAbGroup _ _ _ _ _
  isOrderedAbGroupℝ .isAbGroup       = isAGℝ+
  isOrderedAbGroupℝ .isPseudolattice = isPLℝ≤
  isOrderedAbGroupℝ .isStrictOrder   = isSOℝ<
  isOrderedAbGroupℝ .<-≤-weaken      = λ x y   → ℝ.<Weaken≤ {x} {y}
  isOrderedAbGroupℝ .≤≃¬>            = λ x y   → ℝ.≤≃¬> {x} {y}
  isOrderedAbGroupℝ .<-≤-trans       = λ x y z → ℝ.isTrans<≤ {x} {y} {z}
  isOrderedAbGroupℝ .≤-<-trans       = λ x y z → ℝ.isTrans≤< {x} {y} {z}
  isOrderedAbGroupℝ .+MonoR≤         = λ x y z → ℝ.+MonoR≤ {x} {y} {z}
  isOrderedAbGroupℝ .+MonoR<         = λ x y z → ℝ.+MonoR< {x} {y} {z}
  isOrderedAbGroupℝ .posSum→pos∨pos  = λ x y   → ℝ.posSum→pos∨pos {x} {y}
