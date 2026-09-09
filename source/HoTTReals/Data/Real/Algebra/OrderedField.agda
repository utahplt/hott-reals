module HoTTReals.Data.Real.Algebra.OrderedField where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Morphisms

open import Cubical.Relation.Premetric.Completion.Instances.HIITReals as ℝ hiding (
  _+_ ; -_)

open import HoTTReals.Algebra.HeytingField.Base
open import HoTTReals.Algebra.OrderedField.Base
open import HoTTReals.Algebra.OrderedField.Instances.Rationals
open import HoTTReals.Data.Real.Algebra.Addition as ℝ
open import HoTTReals.Data.Real.Algebra.Multiplication as ℝ hiding (_·_)
open import HoTTReals.Data.Real.Algebra.OrderedCommRing as ℝ
open import HoTTReals.Data.Real.Algebra.Reciprocal as ℝ hiding (#0→isInv ; isInv→#0)
open import HoTTReals.Data.Real.Order.Base as ℝ hiding (_<_ ; _≤_)

open OrderedFieldStr

ℝOrderedField : OrderedField ℓ-zero ℓ-zero
fst ℝOrderedField = ℝ
0f  (snd ℝOrderedField) = 0
1f  (snd ℝOrderedField) = 1
_+_ (snd ℝOrderedField) = ℝ._+_
_·_ (snd ℝOrderedField) = ℝ._·_
-_  (snd ℝOrderedField) = ℝ.-_
_<_ (snd ℝOrderedField) = ℝ._<_
_≤_ (snd ℝOrderedField) = ℝ._≤_
isOrderedField (snd ℝOrderedField) = isOrderedFieldℝ
  where
  open IsOrderedField
  open OrderedCommRingStr (snd ℝOrderedCommRing) renaming (isOrderedCommRing to isOCRℝ)

  isOrderedFieldℝ : IsOrderedField _ _ _ _ _ _ _
  isOrderedFieldℝ .isOrderedCommRing = isOCRℝ
  isOrderedFieldℝ .#0→isInv          = ℝ.#0→isInv
  isOrderedFieldℝ .isInv→#0          = ℝ.isInv→#0

ratᶠ : OrderedFieldHom ℚOrderedField ℝOrderedField
fst ratᶠ = rat
snd ratᶠ = isOFHom module IsOrderedFieldHomrat where
  open IsOrderedCommRingMono renaming (isOrderedCommRingHom to isOCRHom)
  open IsOrderedCommRingHom  renaming (isCommRingHom        to isCRHom)
  open IsCommRingHom
  isOFHom : IsOrderedFieldHom (snd ℚOrderedField) rat (snd ℝOrderedField)
  isOFHom .isOCRHom .isCRHom .pres0 = refl
  isOFHom .isOCRHom .isCRHom .pres1 = refl
  isOFHom .isOCRHom .isCRHom .pres+ = λ _ _ → refl
  isOFHom .isOCRHom .isCRHom .pres· = (sym ∘_) ∘ rat·rat
  isOFHom .isOCRHom .isCRHom .pres- = λ _ → refl
  isOFHom .isOCRHom .pres≤    = λ _ _ → equivFun ≤≃rat≤
  isOFHom .isOCRHom .reflect< = λ _ _ → invEq <≃rat<
  isOFHom .pres< = λ _ _ → equivFun <≃rat<

ℝHeytingField : HeytingField ℓ-zero ℓ-zero
ℝHeytingField = OrderedField→HeytingField ℝOrderedField
