module HoTTReals.Relation.Premetric.Completion.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP using (⟨_⟩)

open import Cubical.Relation.Premetric
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Base using (ι)
open import Cubical.Relation.Premetric.Completion.Properties renaming
  (ℭPremetricSpace to ℭ)
open import Cubical.Relation.Premetric.Completion.Lift

private
  variable
    ℓA ℓA' ℓB ℓB' ℓN ℓN' : Level

module _
  (A : PremetricSpace ℓA (ℓ-max ℓA ℓA'))
  (B : PremetricSpace ℓB (ℓ-max ℓB ℓB'))
  (N : PremetricSpace ℓN' ℓN) where
  private
    ℭA = ℭ ℓA' A
    ℭB = ℭ ℓB' B

  continuous₂≡ :
    (f g : ⟨ ℭA ⟩ → ⟨ ℭB ⟩ → ⟨ N ⟩) →
    ((u : ⟨ ℭA ⟩) → isContinuous (snd ℭB) (f u) (snd N)) →
    ((v : ⟨ ℭB ⟩) → isContinuous (snd ℭA) (flip f v) (snd N)) →
    ((u : ⟨ ℭA ⟩) → isContinuous (snd ℭB) (g u) (snd N)) →
    ((v : ⟨ ℭB ⟩) → isContinuous (snd ℭA) (flip g v) (snd N)) →
    ((a : ⟨ A ⟩) (b : ⟨ B ⟩) → f (ι a) (ι b) ≡ g (ι a) (ι b)) →
    (u : ⟨ ℭA ⟩) (v : ⟨ ℭB ⟩) → f u v ≡ g u v
  continuous₂≡ = {!!}
