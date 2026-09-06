module HoTTReals.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric

open PositiveRationals

private
  variable
    ℓ ℓ' : Level

module _ (M : PremetricSpace ℓ ℓ') where
  open PremetricTheory M

  IsEventuallyConstantAt : (ℚ₊ → ⟨ M ⟩) → ⟨ M ⟩ → ℚ₊ → Type ℓ
  IsEventuallyConstantAt x c θ = (δ : ℚ₊) → δ <₊ θ → x δ ≡ c

  isLimit→isEventuallyConstantAt→≡ :
    {x : ℚ₊ → ⟨ M ⟩} {l c : ⟨ M ⟩} {θ : ℚ₊} →
    isLimit x l →
    IsEventuallyConstantAt x c θ →
    l ≡ c
  isLimit→isEventuallyConstantAt→≡ = {!!}
