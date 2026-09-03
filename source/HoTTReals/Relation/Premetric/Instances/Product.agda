module HoTTReals.Relation.Premetric.Instances.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Product

open PositiveRationals

private
  variable
    ℓM ℓM' ℓN ℓN' ℓX ℓX' : Level

module _
  (M : PremetricSpace ℓM ℓM')
  (N : PremetricSpace ℓN ℓN')
  (X : PremetricSpace ℓX ℓX') where

  uncurryIsLipschitzWith
    : (h : ⟨ M ⟩ → ⟨ N ⟩ → ⟨ X ⟩) (L₁ L₂ : ℚ₊)
    → ((y : ⟨ N ⟩) → IsLipschitzWith (snd M) (flip h y) (snd X) L₁)
    → ((x : ⟨ M ⟩) → IsLipschitzWith (snd N) (h x)      (snd X) L₂)
    → IsLipschitzWith (snd (M ×PrSp N)) (uncurry h) (snd X) (L₁ +₊ L₂)
  uncurryIsLipschitzWith h L₁ L₂ leftLipschitz rightLipschitz = {!!}

  uncurryNE₂ : NE₂[ M , N , X ] → L[ M ×PrSp N , X ]
  uncurryNE₂ f = {!!}
