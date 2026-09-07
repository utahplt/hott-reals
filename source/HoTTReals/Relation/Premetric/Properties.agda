module HoTTReals.Relation.Premetric.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric

open PositiveRationals
open PositiveHalvesℚ

private
  variable
    ℓ ℓ' : Level

module _ (M : PremetricSpace ℓ ℓ') where
  open PremetricStr (snd M)
  open PremetricTheory M

  IsEventuallyConstantAt : (ℚ₊ → ⟨ M ⟩) → ⟨ M ⟩ → ℚ₊ → Type ℓ
  IsEventuallyConstantAt x c θ = (δ : ℚ₊) → δ <₊ θ → x δ ≡ c

  isLimit→isEventuallyConstantAt→≡ :
    {x : ℚ₊ → ⟨ M ⟩} {l c : ⟨ M ⟩} (θ : ℚ₊) →
    isLimit x l →
    IsEventuallyConstantAt x c θ →
    l ≡ c
  isLimit→isEventuallyConstantAt→≡ {x} {l} {c} θ lIsLimit isEventuallyConstant =
    isSeparated≈ l c close
    where
    close : (ε : ℚ₊) → l ≈[ ε ] c
    close ε =
      isSym≈ c l ε
        ( subst≈L
          ( isEventuallyConstant δ (min/2₊<L θ ε))
          ( isLimit≈< x l lIsLimit δ ε (min/2₊<R θ ε)))
      where
      δ : ℚ₊
      δ = min₊ θ ε /2₊
