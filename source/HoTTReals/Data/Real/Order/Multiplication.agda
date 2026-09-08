module HoTTReals.Data.Real.Order.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Cubical.HITs.PropositionalTruncation as PT using ()

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Multiplication
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base

open PositiveRationals
open OrderedAbGroupTheory ℝOrderedAbGroup using (<→0<Δ ; 0<Δ→<)

·MonoR≤ : {x y a : ℝ} → 0 ≤ a → x ≤ y → x · a ≤ y · a
·MonoR≤ {x} {y} {a} 0≤a x≤y = {!!}

0<· : {x y : ℝ} → 0 < x → 0 < y → 0 < x · y
0<· {x} {y} 0<x 0<y = {!!}

·MonoL< : {y z a : ℝ} → 0 < a → y < z → a · y < a · z
·MonoL< {y} {z} {a} 0<a y<z = {!!}

·MonoR< : {x y a : ℝ} → 0 < a → x < y → x · a < y · a
·MonoR< {x} {y} {a} 0<a x<y = {!!}
