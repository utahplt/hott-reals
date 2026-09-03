module HoTTReals.Relation.Premetric.Mappings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Data.Rationals as ℚ using ()

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings

open PositiveRationals

private
  variable
    ℓM ℓM' ℓN ℓN' ℓO ℓO' : Level

module _
  {M : PremetricSpace ℓM ℓM'}
  {N : PremetricSpace ℓN ℓN'}
  {O : PremetricSpace ℓO ℓO'} where

  composeIsLipschitzWith :
    (g : ⟨ N ⟩ → ⟨ O ⟩) (f : ⟨ M ⟩ → ⟨ N ⟩) (R L : ℚ₊) →
    IsLipschitzWith (snd N) g (snd O) R →
    IsLipschitzWith (snd M) f (snd N) L →
    IsLipschitzWith (snd M) (g ∘ f) (snd O) (R ·₊ L)
  IsLipschitzWith.pres≈
    (composeIsLipschitzWith g f R L gLipschitz fLipschitz) x y ε =
    subst≈ (g (f x)) (g (f y)) (ℚ.·Assoc ⟨ R ⟩₊ ⟨ L ⟩₊ ⟨ ε ⟩₊) ∘
    gLipschitz .pres≈ (f x) (f y) (L ·₊ ε) ∘
    fLipschitz .pres≈ x y ε
    where
      open IsLipschitzWith
      open PremetricTheory O
