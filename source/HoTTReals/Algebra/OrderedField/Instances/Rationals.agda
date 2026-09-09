module HoTTReals.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Field.Instances.Rationals using
  ( 0≢1-ℚ ; hasInverseℚ)
open import Cubical.Algebra.OrderedCommRing.Base using (OrderedCommRingStr)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using
  ( ℚOrderedCommRing)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ using ()
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)

open import HoTTReals.Algebra.OrderedField.Base

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField =
  ℚ , orderedfieldstr 0 1 ℚ._+_ ℚ._·_ ℚ.-_ ℚ._<_ ℚ._≤_ isOrderedFieldℚ
  where
  isInv→#0ℚ : (x y : ℚ) → x ℚ.· y ≡ 1 → (x ℚ.< 0) ⊎ (0 ℚ.< x)
  isInv→#0ℚ x y xy≡1 with x ℚ.≟ 0
  ... | ℚ.lt x<0 = inl x<0
  ... | ℚ.eq x≡0 =
    ⊥.rec $ 0≢1-ℚ $
      sym (ℚ.·AnnihilL y) ∙ cong (ℚ._· y) (sym x≡0) ∙ xy≡1
  ... | ℚ.gt 0<x = inr 0<x

  isOrderedFieldℚ : IsOrderedField 0 1 ℚ._+_ ℚ._·_ ℚ.-_ ℚ._<_ ℚ._≤_
  IsOrderedField.isOrderedCommRing isOrderedFieldℚ =
    OrderedCommRingStr.isOrderedCommRing $ snd ℚOrderedCommRing
  IsOrderedField.#0→isInv isOrderedFieldℚ x x#0 =
    hasInverseℚ x $ λ x≡0 → ℚ.isIrrefl# 0 $ subst (ℚ._# 0) x≡0 x#0
  IsOrderedField.isInv→#0 isOrderedFieldℚ = isInv→#0ℚ
