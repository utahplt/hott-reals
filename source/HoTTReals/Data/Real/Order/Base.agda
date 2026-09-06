module HoTTReals.Data.Real.Order.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Data.Real.Algebra.Lattice

open BinaryRelation

_≤_ : ℝ → ℝ → Type ℓ-zero
x ≤ y = max x y ≡ y

infix 4 _≤_

isProp≤ : isPropValued _≤_
isProp≤ = {!!}

isRefl≤ : isRefl _≤_
isRefl≤ = {!!}

isAntisym≤ : isAntisym _≤_
isAntisym≤ = {!!}

isTrans≤ : isTrans _≤_
isTrans≤ = {!!}

ℝ≤Poset : Poset ℓ-zero ℓ-zero
fst ℝ≤Poset = ℝ
PosetStr._≤_ (snd ℝ≤Poset) = _≤_
PosetStr.isPoset (snd ℝ≤Poset) = {!!}

≤≃min : {x y : ℝ} → (x ≤ y) ≃ (x ≡ min x y)
≤≃min {x} {y} = {!!}

min≤L : {x y : ℝ} → min x y ≤ x
min≤L = {!!}

min≤R : {x y : ℝ} → min x y ≤ y
min≤R = {!!}

minGLB : {x a b : ℝ} → x ≤ a → x ≤ b → x ≤ min a b
minGLB = {!!}

L≤max : {x y : ℝ} → x ≤ max x y
L≤max = {!!}

R≤max : {x y : ℝ} → y ≤ max x y
R≤max = {!!}

maxLUB : {x a b : ℝ} → a ≤ x → b ≤ x → max a b ≤ x
maxLUB = {!!}

ℝ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℝ≤Pseudolattice = {!!}
