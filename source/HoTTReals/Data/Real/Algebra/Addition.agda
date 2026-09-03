module HoTTReals.Data.Real.Algebra.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open PositiveRationals

+InvRIsLipschitzWith :
  IsLipschitzWith
    (snd ℝPremetricSpace)
    (λ x → x + (- x))
    (snd ℝPremetricSpace)
    2
+InvRIsLipschitzWith = {!!}

+InvR : (x : ℝ) → x + (- x) ≡ 0
+InvR = {!!}

ℝAbGroup : AbGroup ℓ-zero
ℝAbGroup = {!!}
