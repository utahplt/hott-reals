module HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import HoTTReals.Algebra.OrderedAbGroup.Base
open import HoTTReals.Algebra.OrderedCommRing.Properties

ℚOrderedAbGroup : OrderedAbGroup ℓ-zero ℓ-zero
ℚOrderedAbGroup = OrderedCommRing→OrderedAbGroup ℚOrderedCommRing
