module HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import HoTTReals.Algebra.OrderedAbGroup.Base

ℚOrderedAbGroup : OrderedAbGroup ℓ-zero ℓ-zero
ℚOrderedAbGroup = OrderedCommRing→OrderedAbGroup ℚOrderedCommRing
