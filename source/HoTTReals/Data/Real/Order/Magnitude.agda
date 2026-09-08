module HoTTReals.Data.Real.Order.Magnitude where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()

open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; squash₁)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  ( ℚPremetricSpace)
open import Cubical.Relation.Premetric.Completion.Elim ℚPremetricSpace using
  ( Elimℭ-Prop)
open import Cubical.Relation.Premetric.Completion.Closeness
  ℓ-zero ℚPremetricSpace using (∼≃B)
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Algebra.OrderedAbGroup.Properties
open import HoTTReals.Algebra.OrderedAbGroup.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Addition
open import HoTTReals.Data.Real.Algebra.Lattice
open import HoTTReals.Data.Real.Algebra.OrderedAbGroup
open import HoTTReals.Data.Real.Order.Base
open import HoTTReals.Data.Real.Order.Addition

open PositiveRationals
open OrderedAbGroupTheory ℝOrderedAbGroup using
  ( abs ; 0≤abs ; abs≤≃ ; absΔabs≤ ; abs<→< ; abs<→-<)
open OrderedAbGroupTheory ℚOrderedAbGroup using () renaming (abs to absℚ)

abs∘rat : (q : ℚ) → abs (rat q) ≡ rat (absℚ q)
abs∘rat = {!!}

∼→Δ≤rat : {x y : ℝ} {ε : ℚ₊} → x ∼[ ε ] y → y - x ≤ rat ⟨ ε ⟩₊
∼→Δ≤rat {x} {y} {ε} = {!!}

-rat<→<rat→∼0 :
  {d : ℝ} {ε : ℚ₊} → - rat ⟨ ε ⟩₊ < d → d < rat ⟨ ε ⟩₊ → d ∼[ ε ] 0
-rat<→<rat→∼0 {d} {ε} = {!!}

∼≃abs< : {x y : ℝ} {ε : ℚ₊} → (x ∼[ ε ] y) ≃ (abs (x - y) < rat ⟨ ε ⟩₊)
∼≃abs< {x} {y} {ε} = {!!}

absⁿ : NE[ ℝPremetricSpace , ℝPremetricSpace ]
fst absⁿ = abs
snd absⁿ = {!!}

∃abs<rat : (x : ℝ) → ∃[ q ∈ ℚ₊ ] (abs x < rat ⟨ q ⟩₊)
∃abs<rat = {!!}
