module HoTTReals.Data.Real.Algebra.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚ using ()

open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Completion.Lift
open import Cubical.Relation.Premetric.Completion.Instances.HIITReals

open import HoTTReals.Relation.Premetric.Mappings
open import HoTTReals.Relation.Premetric.Instances.Product

open PositiveRationals

+InvRIsLipschitzWith :
  IsLipschitzWith
    (snd ℝPremetricSpace)
    (λ x → x + (- x))
    (snd ℝPremetricSpace)
    2
+InvRIsLipschitzWith =
  subst
    (IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → x + (- x))
      (snd ℝPremetricSpace))
    (ℚ₊≡ refl)
    (composeIsLipschitzWith
      (uncurry _+_)
      (fst pairing)
      (1 +₊ 1)
      1
      (uncurryIsLipschitzWith
        _
        _
        _
        _+_
        1
        1
        (isNonExpansive→isLipschitzWith1 _ _ _ ∘ lNE)
        (isNonExpansive→isLipschitzWith1 _ _ _ ∘ rNE))
      (isNonExpansive→isLipschitzWith1 _ _ _ (snd pairing)))
  where
    open NE₂[_,_,_] +NE₂

    pairing : NE[ ℝPremetricSpace , ℝPremetricSpace ×PrSp ℝPremetricSpace ]
    pairing = ⟨_,_⟩ⁿ _ _ idⁿ -ⁿ

+InvR : (x : ℝ) → x + (- x) ≡ 0
+InvR =
  continuous≡
    _
    _
    (L→C ((λ x → x + (- x)) , ∣ 2 , +InvRIsLipschitzWith ∣₁))
    (constᶜ 0)
    (cong rat ∘ ℚ.+InvR)

ℝAbGroup : AbGroup ℓ-zero
ℝAbGroup = makeAbGroup 0 _+_ -_ isSetℭ +Assoc +IdR +InvR +Comm
