module HoTTReals.Data.Real.Algebra.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using ()

open import Cubical.Algebra.AbGroup

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Lift
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Relation.Premetric.Mappings
open import HoTTReals.Relation.Premetric.Instances.Product

+InvR : (x : ℝ) → x + (- x) ≡ 0
+InvR =
  lipschitz≡
    ( _)
    ( _)
    ( composeNE₂ _ _ _ idⁿ -ⁿ +NE₂)
    ( constᴸ 0)
    ( cong rat ∘ ℚ.+InvR)

ℝAbGroup : AbGroup ℓ-zero
fst ℝAbGroup = ℝ
AbGroupStr.0g  (snd ℝAbGroup) = 0
AbGroupStr._+_ (snd ℝAbGroup) = _+_
AbGroupStr.-_  (snd ℝAbGroup) = -_
AbGroupStr.isAbGroup (snd ℝAbGroup) = isAbGroupℝ
  where opaque
    isAbGroupℝ : IsAbGroup 0 _+_ (-_)
    isAbGroupℝ = makeIsAbGroup isSetℭ +Assoc +IdR +InvR +Comm
