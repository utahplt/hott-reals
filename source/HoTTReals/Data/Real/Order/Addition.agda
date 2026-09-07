module HoTTReals.Data.Real.Order.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using ()
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Lift
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedCommRing.Properties
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Relation.Premetric.Instances.Product
open import HoTTReals.Relation.Premetric.Mappings

-DistMin : (x y : ℝ) → - min x y ≡ max (- x) (- y)
-DistMin = {!!}

-Flip≤ : {x y : ℝ} → x ≤ y → - y ≤ - x
-Flip≤ {x} {y} = {!!}

+DistRMax :
  (a x y : ℝ) → a + max x y ≡ max (a + x) (a + y)
+DistRMax = {!!}

+MonoL≤ : {x y a : ℝ} → x ≤ y → a + x ≤ a + y
+MonoL≤ {x} {y} {a} = {!!}

+MonoR≤ : {x y a : ℝ} → x ≤ y → x + a ≤ y + a
+MonoR≤ {x} {y} {a} = {!!}

